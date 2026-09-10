#!/usr/bin/env python3
# CAMERA_TROLINK_IDLE_ADAPTIVE_FIX_V2: balanced streaming classifier + adaptive Trolink idle detection.
# Replaces the previous over-sensitive camera/NVR candidate policy; LAN discovery remains sensitivity-oriented.
import sys
import hashlib
import os
import re
import csv
import json
import subprocess
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox
from pathlib import Path
from datetime import datetime
import urllib.request
import shutil
import signal
import struct
import ipaddress
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
MAC_FULL = re.compile(r"^(?:[0-9a-fA-F]{2}:){5}[0-9a-fA-F]{2}$")
MAC_FIND = re.compile(r"(?:[0-9a-fA-F]{2}:){5}[0-9a-fA-F]{2}")
VENDOR_CACHE = Path.home() / ".wifi_audit_vendor_cache.json"


# ============================================================
# AVVIO PORTABILE
# ============================================================
# Percorso reale dello script, indipendente dalla cartella corrente.
PROGRAM_FILE = Path(__file__).resolve()
PROGRAM_DIR = PROGRAM_FILE.parent

# Tutti i percorsi relativi e i file di lavoro partono dalla cartella
# nella quale si trova wifi300.py.
try:
    os.chdir(str(PROGRAM_DIR))
except Exception:
    pass

REAL_USER = (os.environ.get("SUDO_USER") or os.environ.get("USER") or "").strip()


# Callback globale usata dalla finestra DEBUG COMANDI.
COMMAND_DEBUG_CALLBACK = None

def _debug_command(cmd, source="CMD"):
    """Registra un comando nella finestra DEBUG, se disponibile."""
    global COMMAND_DEBUG_CALLBACK
    try:
        if isinstance(cmd, (list, tuple)):
            rendered = " ".join(str(x) for x in cmd)
        else:
            rendered = str(cmd)
        if COMMAND_DEBUG_CALLBACK:
            COMMAND_DEBUG_CALLBACK(source, rendered)
    except Exception:
        pass

def popen_logged(cmd, *args, **kwargs):
    """Esegue subprocess.Popen registrando prima il comando."""
    _debug_command(cmd, "POPEN")
    return subprocess.Popen(cmd, *args, **kwargs)

def run(cmd, timeout=None):
    """Esegue un comando e restituisce sempre un oggetto con returncode/stdout/stderr."""
    try:
        _debug_command(cmd, "RUN")
        return subprocess.run(
            cmd,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False
        )
    except Exception as e:
        class R:
            returncode = 999
            stdout = ""
            stderr = str(e)
        return R()


def load_vendor_cache():
    try:
        if VENDOR_CACHE.exists():
            return json.loads(VENDOR_CACHE.read_text(encoding="utf-8"))
    except Exception:
        pass
    return {}

def save_vendor_cache(cache):
    try:
        VENDOR_CACHE.write_text(json.dumps(cache, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass

def lookup_vendor(mac, cache):
    mac = mac.lower()
    if mac in cache:
        return cache[mac]
    try:
        req = urllib.request.Request(
            "https://api.macvendors.com/" + mac,
            headers={"User-Agent": "WiFiPassiveAudit/5.0"}
        )
        with urllib.request.urlopen(req, timeout=3) as r:
            vendor = r.read().decode("utf-8", errors="replace").strip()
            if vendor:
                cache[mac] = vendor
                save_vendor_cache(cache)
                return vendor
    except Exception:
        pass
    return "Sconosciuto"

class App:
    def __init__(self, root):
        self.root = root
        root.title("wifi_402 - EN")
        # Avvio automatico a tutto schermo.
        # Adattamento automatico alla risoluzione disponibile.
        self.screen_width = max(800, int(root.winfo_screenwidth()))
        self.screen_height = max(600, int(root.winfo_screenheight()))

        # Scala generale rispetto alla GUI di riferimento 1380x900.
        # v198: la scala segue realmente la risoluzione disponibile e può
        # scendere maggiormente sugli schermi bassi (es. 1366x768 / 1280x720).
        try:
            self._base_tk_scaling = float(root.tk.call("tk", "scaling"))
        except Exception:
            self._base_tk_scaling = 1.0

        self.ui_scale = min(
            1.0,
            self.screen_width / 1380.0,
            self.screen_height / 900.0
        )
        self.ui_scale = max(0.58, self.ui_scale)

        try:
            root.tk.call(
                "tk", "scaling",
                max(0.60, self._base_tk_scaling * self.ui_scale)
            )
        except Exception:
            pass

        root.geometry(f"{self.screen_width}x{self.screen_height}+0+0")
        root.minsize(800, 600)
        root.attributes("-fullscreen", True)

        # ESC permette di uscire dal tutto schermo; F11 lo attiva/disattiva.
        root.bind("<Escape>", lambda _e: root.attributes("-fullscreen", False))
        root.bind(
            "<F11>",
            lambda _e: root.attributes(
                "-fullscreen",
                not bool(root.attributes("-fullscreen"))
            )
        )

        # Tasto MENO: riduce esclusivamente l'altezza della GUI.
        # La larghezza corrente resta invariata.
        root.bind("-", self._reduce_gui_vertical_only)
        root.bind("<KP_Subtract>", self._reduce_gui_vertical_only)
        root.bind("+", self._increase_gui_vertical_only)
        root.bind("<KP_Add>", self._increase_gui_vertical_only)

        # Tutti i file generati dal programma vengono salvati in una
        # sottocartella "wifi_audit_gui" accanto allo script in esecuzione.
        # In questo modo la cartella non viene più creata nella HOME utente.
        self.program_file = PROGRAM_FILE
        self.program_dir = PROGRAM_DIR
        self.outdir = self.program_dir / "wifi_audit_gui"
        self.outdir.mkdir(parents=True, exist_ok=True)

        # Archivio definitivo delle catture richieste dall'utente.
        # Viene creato automaticamente accanto al programma.
        self.captures_dir = self.program_dir / "CATTURE"
        self.captures_dir.mkdir(parents=True, exist_ok=True)

        self.iface = tk.StringVar()
        self.iface_origin = tk.StringVar(value=": --")
        self.monitor_mode_state = tk.StringVar(value="MONITOR MODE: OFF")
        self.active_monitor_iface = ""

        # Modalità grafica diurna/notturna.
        self.night_mode = False
        self.language = "en"
        self.operation_mode = "idle"
        self.theme_button_text = tk.StringVar(value="VERSIONE\nNOTTURNA")

        # Conserva le funzioni originali dei dialoghi. I wrapper installati più
        # sotto traducono automaticamente AVVISI / ERRORI / INFO in inglese
        # quando la GUI è in modalità ENG.
        self._messagebox_showerror_original = messagebox.showerror
        self._messagebox_showwarning_original = messagebox.showwarning
        self._messagebox_showinfo_original = messagebox.showinfo
        self.bssid = tk.StringVar()
        self.channel = tk.StringVar()
        self.client = tk.StringVar()

        # Titoli dinamici dei pannelli operativi.
        self.passive_box_title = tk.StringVar(value="CATTURA PASSIVA   BSSID: --")
        self.disturb_box_title = tk.StringVar(value="DISTURBO   BSSID: -- / CLIENT: --")
        self.capture_duration = tk.StringVar(value="120")
        self.disturb_duration = tk.StringVar(value="5")
        self.duration = self.disturb_duration
        self.repetitions = tk.StringVar(value="10")
        self.pause_seconds = tk.StringVar(value="3")
        self.countdown = tk.StringVar(value="Pronto")
        self.progress_value = tk.DoubleVar(value=0.0)
        self.progress_text = tk.StringVar(value="0%")
        self.progress_caption = tk.StringVar(value="AVANZAMENTO CATTURA: 0%")
        self.capture_completed_pct = tk.StringVar(value="0%")
        self.capture_progress_value = tk.DoubleVar(value=0.0)
        # Colore corrente della barra BLOCCO/CATTURA:
        # blu per cattura passiva, rosso per disturbo/blocchi.
        self.work_progress_color = "blue"
        self.phase = tk.StringVar(value="PRONTO")
        self.work_detail = tk.StringVar(value="In attesa di avvio")
        self.status = tk.StringVar(value="Pronto")
        self.client_count = tk.StringVar(value="Numero: 0")
        self.camera_number_text = tk.StringVar(value="Numero: 0")
        self.lan_count = tk.StringVar(value="LAN candidati: 0")
        self.other_count = tk.StringVar(value="Altro/incerto: 0")
        self.probable_lan_vendor_count = tk.StringVar(value="Numero: 0")
        # Scansione LAN attiva: usa la rete IP locale del PC, separata dall'analisi PCAP.
        self.active_lan_scan_running = False
        self.active_lan_results = {}
        self.active_lan_scan_info = {}
        self.lan_gateway_info = {}
        self.lan_persistent_rows = {}
        self.lan_persistent_details = {}

        # Memoria cumulativa del grafico: nasce all'apertura del programma e
        # resta valida fino alla chiusura. Le scansioni successive NON la azzerano.
        self._network_graph_history = {
            "routers": {}, "clients": {}, "lans": {}, "cameras": {}
        }
        self._network_graph_relations = []
        # MAC osservati direttamente come station Wi-Fi del BSSID nella sessione.
        # Questa prova radio ha priorità assoluta sulla discovery LAN IP locale.
        self.wifi_radio_macs_session = set()
        # Stabilizzazione tabella LAN: un MAC deve risultare coerente per
        # più aggiornamenti consecutivi prima di essere visualizzato.
        self.lan_candidate_confirmations = {}
        self.lan_confirmed_visible = set()

        self.ap_client_counts = {}
        self.active_lan_results = {}
        self.active_lan_scan_info = {}

        self.manuf_oui_cache = None
        self.capture_file = None
        self.handshake_check_running = False
        self.handshake_found_async = False
        self.handshake_state = tk.StringVar(value="ASSENTE")
        # Visualizzazione handshake semplice, come nello schema richiesto:
        # una riga separata per M1/M2/M3/M4 e stato finale in basso.
        self.handshake_m1 = tk.StringVar(value="--")
        self.handshake_m2 = tk.StringVar(value="--")
        self.handshake_m3 = tk.StringVar(value="--")
        self.handshake_m4 = tk.StringVar(value="--")
        self.handshake_detail = tk.StringVar(value="")  # mantenuto solo per compatibilità interna/log
        self.handshake_string = tk.StringVar(value="")
        self.pmkid_state = tk.StringVar(value="PMKID: non osservato")
        self.ap_scan_progress = tk.DoubleVar(value=0.0)
        self.ap_scan_progress_text = tk.StringVar(value="0%")
        self.client_scan_progress = tk.DoubleVar(value=0.0)
        self.client_scan_progress_text = tk.StringVar(value="0%")
        self.client_search_caption = tk.StringVar(
            value="Ricerca Client Associati a: --"
        )

        # Valori mostrati nel nuovo riquadro BLOCCO in basso a destra.
        # Per ora il riquadro è solo grafico: i pulsanti non eseguono comandi.
        self.block_router_value = tk.StringVar(value="")
        self.block_client_value = tk.StringVar(value="")

        # Processi esterni separati per BLOCCO ROUTER e BLOCCO CLIENT.
        self.aireplay_ng_router_process = None
        self.aireplay_ng_router_blink_after = None
        self.aireplay_ng_router_blink_phase = False

        self.aireplay_ng_client_process = None
        self.aireplay_ng_client_blink_after = None
        self.aireplay_ng_client_blink_phase = False

        # Stato persistente del lampeggio BLOCCO: un semplice errore grafico
        # o ridisegno non deve spegnere il lampeggio mentre il processo è attivo.
        self.aireplay_ng_router_blink_running = False
        self.aireplay_ng_client_blink_running = False

        self.ap_scan_stop = threading.Event()
        self.ap_scan_pause = threading.Event()
        self.ap_scan_finished = True
        self.ap_scan_process = None

        # Ordinamento manuale ROUTER RILEVATI.
        # Abilitato solo quando la scansione è in pausa o terminata.
        self.ap_manual_sort_column = None
        self.ap_manual_sort_desc = True

        self.client_scan_process = None
        self.client_scan_pause = threading.Event()
        self.client_scan_finished = True

        # Ordinamento manuale DISPOSITIVI CLIENT WIFI.
        # Utilizzabile soltanto con ricerca client in pausa o terminata.
        self.client_manual_sort_column = None
        self.client_manual_sort_desc = True
        self.handshake_pairs = set()
        self._tshark_fields_cache = None
        self.stop_on_handshake = tk.BooleanVar(value=False)
        self.stop_on_handshake_event = threading.Event()
        # Stato "latched": una volta trovato un 4-way completo, la GUI non
        # viene più azzerata da controlli successivi finché non parte una nuova sessione.
        self.handshake_latched = False
        self.handshake_latched_text = ""
        self.handshake_latched_msgs = set()

        self.diegi_stop = threading.Event()
        self.diegi_process = None
        self.diegi_running = False

        # Arresto coordinato della cattura PCAP (airodump-ng).
        self.capture_stop = threading.Event()
        self.capture_process = None
        # Identificatore univoco della sessione di cattura.
        # Serve a impedire che un vecchio worker, fermato manualmente,
        # possa aggiornare la barra o portarla al 100% dopo un nuovo AVVIA.
        self.capture_run_id = 0

        # Stato lampeggio pulsanti operativi.
        self._button_blink_after = {}
        self._button_blink_phase = {}
        self._button_blink_running = {}

        # Analisi MAC progressiva durante la cattura.
        self.live_mac_check_running = False
        self.live_mac_rows = {}
        self.lan_seen_rows = {}
        self.lan_candidate_details = {}
        self.lan_detail_window = None

        # Classifica progressiva dei dispositivi con comportamento compatibile
        # con telecamera/video IoT. Il punteggio e' euristico, non una prova certa.
        self.camera_candidate_rows = {}
        self.camera_candidate_details = {}
        self.camera_detail_window = None

        # DEBUG globale dei comandi eseguiti dalla GUI.
        self.command_debug_window = None
        self.command_debug_text = None
        self.command_debug_enabled = True
        self._command_debug_buffer = []

        global COMMAND_DEBUG_CALLBACK
        COMMAND_DEBUG_CALLBACK = self.command_debug_write

        self.build()
        self.apply_language("en")
        self.root.update_idletasks()

        # Controllo dual-band affidabile eseguito dal MAIN LOOP Tkinter.
        # Non dipende dai worker thread, quindi l'avviso non può perdersi
        # per chiamate root.after() effettuate da thread secondari.
        self._dual_band_last_target = ("", "")
        self._dual_band_watch_client_running = False
        self._dual_band_watch_capture_running = False

        # Memoria separata per tipo di azione.
        # Un BSSID già analizzato come CLIENT non viene riproposto per CLIENT,
        # ma può ancora essere proposto per CATTURA PASSIVA, e viceversa.
        self._dual_band_scanned_actions = {
            "client": set(),
            "passive": set(),
        }

        # Memoria delle risposte SI/NO separata tra scansione CLIENT
        # e cattura PASSIVA. Serve anche a neutralizzare i retry temporizzati:
        # una stessa domanda non può comparire più volte.
        self._dual_band_prompt_decisions = {
            "client": set(),
            "passive": set(),
        }

        self._dual_band_watch_started = True
        self.root.after(300, self._dual_band_completion_watcher)

        self._responsive_after_id = None
        self._last_responsive_size = None
        self._theme_responsive_after_ids = []

        # Protezione standby / ripristino dopo resume.
        self._suspend_inhibit_process = None
        self._suspend_inhibit_reasons = set()
        self._resume_watch_after = None
        self._resume_last_wall = time.time()
        self._resume_last_mono = time.monotonic()
        self._resume_preferred_iface = ""
        self._resume_monitor_was_active = False
        self._apply_responsive_layout(
            self.root.winfo_width(),
            self.root.winfo_height()
        )
        self.refresh_interfaces()
        try:
            self._refresh_iface_status_theme()
        except Exception:
            pass
        self._install_translated_messageboxes()
        self.root.after(1500, self._start_resume_watchdog)
        self.root.bind("<Configure>", self._on_root_configure, add="+")
        # Il fullscreen su Kali può assestarsi qualche istante dopo build().
        # Due passaggi ritardati garantiscono l'adattamento alla risoluzione reale.
        self.root.after(
            250,
            lambda: self._apply_responsive_layout(
                self.root.winfo_width(), self.root.winfo_height()
            )
        )
        self.root.after(
            900,
            lambda: self._apply_responsive_layout(
                self.root.winfo_width(), self.root.winfo_height()
            )
        )

    def _increase_gui_vertical_only(self, _event=None):
        """Il tasto + riporta immediatamente la GUI a schermo intero."""
        try:
            # Non usare geometry(): su alcuni window manager sposta la finestra
            # leggermente verso sinistra. Il + deve semplicemente ripristinare
            # il vero fullscreen della GUI.
            self.root.attributes("-fullscreen", True)
            self.root.update_idletasks()
            self.root.after(
                80,
                lambda: self._apply_responsive_layout(
                    self.root.winfo_width(), self.root.winfo_height()
                )
            )
        except Exception as exc:
            try:
                self.logmsg(f"Ripristino schermo intero GUI: {exc}")
            except Exception:
                pass
        return "break"

    def _reduce_gui_vertical_only(self, _event=None):
        """Riduce la GUI soltanto in verticale, lasciando invariata la larghezza."""
        try:
            self.root.update_idletasks()
            current_w = max(800, int(self.root.winfo_width()))
            current_h = max(600, int(self.root.winfo_height()))

            # Se siamo fullscreen, usciamo dal fullscreen mantenendo la larghezza.
            if bool(self.root.attributes("-fullscreen")):
                current_w = max(800, int(self.root.winfo_screenwidth()))
                current_h = max(600, int(self.root.winfo_screenheight()))
                self.root.attributes("-fullscreen", False)
                self.root.update_idletasks()

            new_h = max(600, current_h - 70)
            x = int(self.root.winfo_x())
            y = int(self.root.winfo_y())

            self.root.geometry(f"{current_w}x{new_h}+{x}+{y}")
            self.root.update_idletasks()
            self._apply_responsive_layout(current_w, new_h)
        except Exception as exc:
            try:
                self.logmsg(f"Riduzione verticale GUI: {exc}")
            except Exception:
                pass
        return "break"

    def _apply_responsive_layout(self, width=None, height=None):
        """
        Responsive v198:
        - usa la dimensione REALE della finestra/schermo;
        - aggiorna dinamicamente lo scaling Tk;
        - riduce righe, font e altezza delle Treeview sugli schermi bassi;
        - ridimensiona le colonne partendo sempre dalle larghezze originali;
        - evita riduzioni cumulative e loop di Configure.
        """
        try:
            w = int(width if width is not None else self.root.winfo_width())
            h = int(height if height is not None else self.root.winfo_height())
        except Exception:
            w = int(getattr(self, "screen_width", 1380))
            h = int(getattr(self, "screen_height", 900))

        if w < 500:
            w = int(getattr(self, "screen_width", 1380))
        if h < 400:
            h = int(getattr(self, "screen_height", 900))

        # Scala complessiva rispetto alla GUI di riferimento.
        scale = min(1.0, w / 1380.0, h / 900.0)
        scale = max(0.58, scale)
        self.ui_scale = scale

        # Aggiorna lo scaling Tk anche DOPO un cambio risoluzione/F11.
        try:
            base = float(getattr(self, "_base_tk_scaling", 1.0))
            self.root.tk.call("tk", "scaling", max(0.60, base * scale))
        except Exception:
            pass

        # Profili verticali: comprimono in modo deciso gli schermi bassi.
        if h <= 640:
            heights = {"ap_tree": 2, "client_tree": 1, "lan_vendor_tree": 1, "res_tree": 1, "camera_tree": 1}
            rowheight = 17
            title_font = 10
            normal_font = 8
        elif h <= 720:
            heights = {"ap_tree": 2, "client_tree": 1, "lan_vendor_tree": 1, "res_tree": 2, "camera_tree": 2}
            rowheight = 18
            title_font = 11
            normal_font = 8
        elif h <= 800:
            heights = {"ap_tree": 3, "client_tree": 2, "lan_vendor_tree": 2, "res_tree": 2, "camera_tree": 2}
            rowheight = 20
            title_font = 12
            normal_font = 9
        elif h <= 900:
            heights = {"ap_tree": 4, "client_tree": 2, "lan_vendor_tree": 3, "res_tree": 2, "camera_tree": 2}
            rowheight = 22
            title_font = 13
            normal_font = 9
        elif h <= 1080:
            heights = {"ap_tree": 5, "client_tree": 3, "lan_vendor_tree": 4, "res_tree": 3, "camera_tree": 3}
            rowheight = 24
            title_font = 14
            normal_font = 10
        else:
            heights = {"ap_tree": 6, "client_tree": 4, "lan_vendor_tree": 5, "res_tree": 4, "camera_tree": 4}
            rowheight = 26
            title_font = 15
            normal_font = 10

        for name, rows in heights.items():
            tree = getattr(self, name, None)
            if tree is not None:
                try:
                    tree.configure(height=rows)
                except Exception:
                    pass

        # Riduce anche l'altezza fisica delle righe e i titoli principali.
        try:
            self.style.configure(
                "Treeview",
                rowheight=rowheight,
                font=("TkDefaultFont", normal_font)
            )
            self.style.configure(
                "Treeview.Heading",
                font=("TkDefaultFont", normal_font, "bold")
            )
            self.style.configure(
                "Bold.TLabelframe.Label",
                font=("TkDefaultFont", title_font, "bold")
            )
            # Il pulsante VERSIONE NOTTURNA/DIURNA mantiene SEMPRE
            # la stessa dimensione del testo in entrambi i temi.
            # Non viene più ridotto dal responsive dopo il cambio tema.
            self.style.configure(
                "ThemeToggle.TButton",
                font=("TkDefaultFont", 11, "bold"),
                padding=(12, 10),
                anchor="center"
            )
        except Exception:
            pass

        # Larghezze BASE: mai riusare quelle già scalate.
        base_widths = {
            "ap_tree": {
                "bssid":180, "ch":55, "pwr":100, "essid":300,
                "packets":95, "clients":150, "band":90, "enc":100
            },
            "client_tree": {
                "station":190, "resolved":220, "vendor":220,
                "pwr":80, "packets":90, "probes":280, "source":360
            },
            "lan_vendor_tree": {
                "vendor":285, "role":90, "macs":210, "score":70, "level":220, "source":505
            },
            "res_tree": {
                "mac":145, "vendor":145, "class":135,
                "evidence":190, "notes":220, "source":360
            },
            "camera_tree": {
                "mac":145, "vendor":290, "score":75, "level":140,
                "txrx":72, "provenance":115, "duration":95
            }
        }

        min_widths = {
            "ap_tree": {
                "bssid":90, "ch":35, "pwr":75, "essid":95,
                "packets":55, "clients":55, "band":50, "enc":50
            },
            "client_tree": {
                "station":90, "resolved":80, "vendor":80,
                "pwr":45, "packets":55, "probes":85, "source":150
            },
            "lan_vendor_tree": {
                "vendor":120, "role":70, "macs":100, "score":40, "level":120, "source":210
            },
            "res_tree": {
                "mac":90, "vendor":75, "class":75,
                "evidence":95, "notes":110, "source":150
            },
            "camera_tree": {
                "mac":100, "vendor":170, "score":56, "level":90,
                "txrx":58, "provenance":78, "duration":68
            }
        }

        def resize_tree(name, fallback):
            tree = getattr(self, name, None)
            if tree is None:
                return
            try:
                available = int(tree.winfo_width())
                if available < 100:
                    available = int(fallback)
                available = max(220, available - 12)

                bases = base_widths[name]
                mins = min_widths[name]
                total_base = float(sum(bases.values()))
                factor = min(1.0, available / total_base)

                widths = {
                    col: max(mins[col], int(base * factor))
                    for col, base in bases.items()
                }

                total = sum(widths.values())
                if total < available:
                    # spazio residuo alla colonna descrittiva finale
                    last_col = list(bases.keys())[-1]
                    widths[last_col] += available - total

                # Se i minimi superano lo spazio, scala anche i minimi.
                total = sum(widths.values())
                if total > available:
                    shrink = available / float(total)
                    for col in widths:
                        widths[col] = max(34, int(widths[col] * shrink))

                for col, value in widths.items():
                    tree.column(col, width=value)
            except Exception:
                pass

        resize_tree("ap_tree", max(500, w-30))
        resize_tree("client_tree", max(500, w-30))
        resize_tree("lan_vendor_tree", max(500, w-30))
        resize_tree("res_tree", max(360, int(w*0.45)))
        resize_tree("camera_tree", max(700, int(w*0.62)))

        # Le due tabelle SCANNER devono usare tutta la larghezza disponibile
        # e mantenere chiaramente leggibili tutte le intestazioni.
        def fit_scanner_table(tree, proportions, minimums):
            try:
                available = int(tree.winfo_width())
                if available < 200:
                    available = max(600, int(w) - 28)

                # Margine per bordi della Treeview.
                available = max(500, available - 6)

                cols = list(proportions.keys())
                raw = {
                    col: max(minimums[col], int(available * proportions[col]))
                    for col in cols
                }

                total = sum(raw.values())

                # Se i minimi superano la larghezza, riduci in modo uniforme
                # senza rendere illeggibili le intestazioni.
                if total > available:
                    excess = total - available
                    flexible = [
                        c for c in cols
                        if raw[c] > minimums[c]
                    ]
                    while excess > 0 and flexible:
                        step = max(1, excess // len(flexible))
                        new_flexible = []
                        for col in flexible:
                            reducible = raw[col] - minimums[col]
                            take = min(step, reducible, excess)
                            raw[col] -= take
                            excess -= take
                            if raw[col] > minimums[col]:
                                new_flexible.append(col)
                            if excess <= 0:
                                break
                        flexible = new_flexible

                # Se resta spazio, distribuiscilo proporzionalmente per occupare
                # l'intera porzione orizzontale dello schermo.
                total = sum(raw.values())
                remaining = max(0, available - total)
                if remaining:
                    for i, col in enumerate(cols):
                        if i == len(cols) - 1:
                            raw[col] += remaining
                        else:
                            add = int(remaining * proportions[col])
                            raw[col] += add
                            remaining -= add

                for col in cols:
                    tree.column(
                        col,
                        width=raw[col],
                        minwidth=minimums[col],
                        stretch=True,
                        anchor="center"
                    )
            except Exception:
                pass

        # ROUTER RILEVATI: larghezze studiate affinché BSSID, CH, BANDA,
        # CLIENTS, PACCHETTI, ENC e POTENZA siano sempre comprensibili.
        fit_scanner_table(
            self.ap_tree,
            {
                "bssid": 0.16,
                "ch": 0.06,
                "pwr": 0.11,
                "essid": 0.26,
                "packets": 0.12,
                "clients": 0.10,
                "band": 0.10,
                "enc": 0.09,
            },
            {
                "bssid": 135,
                "ch": 55,
                "pwr": 95,
                "essid": 160,
                "packets": 100,
                "clients": 82,
                "band": 82,
                "enc": 70,
            }
        )

        # DISPOSITIVI CLIENT WIFI: stessa logica su tutta la larghezza.
        fit_scanner_table(
            self.client_tree,
            {
                "station": 0.18,
                "resolved": 0.20,
                "vendor": 0.20,
                "pwr": 0.12,
                "packets": 0.13,
                "probes": 0.17,
            },
            {
                "station": 140,
                "resolved": 145,
                "vendor": 145,
                "pwr": 95,
                "packets": 105,
                "probes": 125,
            }
        )

        # Combobox adattiva.
        try:
            if w < 900:
                self.iface_combo.configure(width=12)
            elif w < 1200:
                self.iface_combo.configure(width=15)
            elif w < 1500:
                self.iface_combo.configure(width=18)
            else:
                self.iface_combo.configure(width=20)
        except Exception:
            pass

        # Su risoluzioni molto basse riduce i padding verticali dei frame principali.
        compact = h <= 800
        try:
            if compact:
                self.style.configure("TButton", padding=(4,2))
                self.style.configure("TEntry", padding=(2,1))
            else:
                self.style.configure("TButton", padding=(6,4))
        except Exception:
            pass
        try:
            self._enforce_tree_heading_theme()
        except Exception:
            pass



    def _refresh_lan_score_font_overlay(self):
        """Usa lo stesso font compatto per SC e PROVENIENZA nella tabella LAN.

        Le Label vengono riutilizzate per evitare lampeggi durante la cattura e
        rispettano automaticamente i colori del tema normale/notturno.
        """
        tree = getattr(self, "lan_vendor_tree", None)
        if tree is None:
            return

        try:
            overlays = getattr(self, "_lan_score_overlay_labels", None)
            if not isinstance(overlays, dict):
                if isinstance(overlays, (list, tuple)):
                    for old_lbl in overlays:
                        try:
                            old_lbl.destroy()
                        except Exception:
                            pass
                overlays = {}
                self._lan_score_overlay_labels = overlays

            geom_cache = getattr(self, "_lan_score_overlay_geometry", None)
            if not isinstance(geom_cache, dict):
                geom_cache = {}
                self._lan_score_overlay_geometry = geom_cache

            state_cache = getattr(self, "_lan_score_overlay_state", None)
            if not isinstance(state_cache, dict):
                state_cache = {}
                self._lan_score_overlay_state = state_cache

            dark = bool(getattr(self, "night_mode", False))
            selected_items = set(tree.selection())
            normal_bg = "#050505" if dark else "#FFFFFF"
            normal_fg = "#D6D8DC" if dark else "#202020"
            selected_bg = "#4A6984"
            selected_fg = "#FFFFFF"
            try:
                st = ttk.Style()
                sbg = st.lookup("Treeview", "background", ("selected",))
                sfg = st.lookup("Treeview", "foreground", ("selected",))
                if sbg:
                    selected_bg = sbg
                if sfg:
                    selected_fg = sfg
            except Exception:
                pass

            current_items = set(tree.get_children())
            valid_keys = {(iid, col) for iid in current_items for col in ("score", "source")}
            for key in list(overlays.keys()):
                if key not in valid_keys:
                    try:
                        overlays[key].destroy()
                    except Exception:
                        pass
                    overlays.pop(key, None)
                    geom_cache.pop(key, None)
                    state_cache.pop(key, None)

            col_index = {"score": 3, "source": 5}
            for item in tree.get_children():
                vals = tree.item(item, "values")
                selected = item in selected_items
                cell_bg = selected_bg if selected else normal_bg
                cell_fg = selected_fg if selected else normal_fg

                for col in ("score", "source"):
                    key = (item, col)
                    bbox = tree.bbox(item, col)
                    lbl = overlays.get(key)
                    if not bbox:
                        if lbl is not None:
                            try:
                                lbl.place_forget()
                            except Exception:
                                pass
                        geom_cache.pop(key, None)
                        continue

                    x, y, width, height = bbox
                    idx = col_index[col]
                    value = vals[idx] if len(vals) > idx else ""

                    if lbl is None or not lbl.winfo_exists():
                        lbl = tk.Label(
                            tree, text=str(value),
                            font=("DejaVu Sans Mono", 9, "normal"),
                            bg=cell_bg, fg=cell_fg, bd=0, highlightthickness=0,
                            anchor="center", padx=0, pady=0
                        )

                        def _lan_overlay_click(_event, iid=item):
                            try:
                                tree.selection_set(iid)
                                tree.focus(iid)
                                self._refresh_lan_score_font_overlay()
                                vals_click = tree.item(iid, "values")
                                if len(vals_click) >= 5:
                                    self._show_lan_detail(str(vals_click[4]).lower())
                            except Exception:
                                pass
                            return "break"

                        lbl.bind("<ButtonRelease-1>", _lan_overlay_click)
                        overlays[key] = lbl

                    new_state = (str(value), str(cell_bg), str(cell_fg))
                    if state_cache.get(key) != new_state:
                        try:
                            lbl.configure(text=str(value), bg=cell_bg, fg=cell_fg)
                            state_cache[key] = new_state
                        except Exception:
                            pass

                    new_geom = (x + 1, y + 1, max(1, width - 2), max(1, height - 2))
                    if geom_cache.get(key) != new_geom:
                        try:
                            lbl.place(x=new_geom[0], y=new_geom[1],
                                      width=new_geom[2], height=new_geom[3])
                            geom_cache[key] = new_geom
                        except Exception:
                            pass
        except Exception:
            pass

    def _refresh_cyborg_label(self):
        """Mantiene la firma Cyborg visibile in basso a sinistra."""
        try:
            label=getattr(self,"cyborg_label",None)
            if label is None or not label.winfo_exists():
                return
            dark=bool(getattr(self,"night_mode",False))
            label.configure(
                bg=("#111111" if dark else self.root.cget("bg")),
                fg=("#8E969C" if dark else "#555555")
            )
            label.place(x=10,rely=1.0,y=-2,anchor="sw")
            label.lift()
        except Exception:
            pass

    def _on_root_configure(self, event):
        """
        Gestisce SOLO il resize della finestra principale.
        Questo evita il loop che si crea se si reagisce ai Configure dei widget figli.
        """
        if event.widget is not self.root:
            return

        size = (int(event.width), int(event.height))
        if size == getattr(self, "_last_responsive_size", None):
            return
        self._last_responsive_size = size

        old = getattr(self, "_responsive_after_id", None)
        if old is not None:
            try:
                self.root.after_cancel(old)
            except Exception:
                pass

        self._responsive_after_id = self.root.after(
            180,
            lambda w=size[0], h=size[1]: self._apply_responsive_layout(w, h)
        )
        try:
            if hasattr(self, "_position_monitor_warning"):
                self.root.after(200, self._position_monitor_warning)
        except Exception:
            pass
        try:
            self.root.after(50,self._refresh_cyborg_label)
        except Exception:
            pass


    def build(self):
        style = ttk.Style(self.root)
        self.style = style
        try:
            style.theme_use("clam")
        except Exception:
            pass

        # Stato iniziale della GUI = VERSIONE DIURNA.
        # "clam" usa un grigio di default per le Treeview: impostiamo qui
        # esplicitamente il bianco, perché apply_display_theme(False) non
        # viene chiamato automaticamente all'avvio.
        style.configure(
            "Treeview",
            background="#FFFFFF",
            fieldbackground="#FFFFFF",
            foreground="#000000"
        )
        style.map(
            "Treeview",
            background=[("selected", "#3478BF")],
            foreground=[("selected", "#FFFFFF")]
        )
        style.configure(
            "Scanner.Treeview",
            background="#FFFFFF",
            fieldbackground="#FFFFFF",
            foreground="#000000"
        )
        style.map(
            "Scanner.Treeview",
            background=[("selected", "#3478BF")],
            foreground=[("selected", "#FFFFFF")]
        )
        style.configure(
            "Camera.Treeview",
            background="#FFFFFF",
            fieldbackground="#FFFFFF",
            foreground="#000000"
        )
        style.map(
            "Camera.Treeview",
            background=[("selected", "#3478BF")],
            foreground=[("selected", "#FFFFFF")]
        )
        style.configure(
            "Treeview.Heading",
            background="#E5E5E5",
            foreground="#000000"
        )

        style.configure(
            "Bold.TLabelframe.Label",
            font=("TkDefaultFont", 15, "bold")
        )
        style.configure(
            "CameraTitle.TLabelframe.Label",
            font=("TkDefaultFont", 17, "bold")
        )
        style.configure(
            "CameraTitle.TLabelframe",
            labelmargins=(8,0,0,0)
        )

        # Tabelle scanner: intestazioni più grandi e leggibili.
        style.configure(
            "Scanner.Treeview",
            rowheight=24
        )
        style.configure(
            "Scanner.Treeview.Heading",
            font=("TkDefaultFont", 10, "bold")
        )
        style.configure(
            "Bold.TLabelframe",
            labelmargins=(8,0,0,0)
        )
        style.configure(
            "ScanBlue.TButton",
            background="#1565c0",
            foreground="white",
            font=("TkDefaultFont", 10, "bold")
        )
        style.map(
            "ScanBlue.TButton",
            background=[("active", "#1976d2"), ("pressed", "#0d47a1")],
            foreground=[("active", "white"), ("pressed", "white")]
        )

        style.configure(
            "Big.TCheckbutton",
            font=("TkDefaultFont", 12, "bold"),
            padding=(12, 10),
            indicatorsize=36,
            indicatormargin=8
        )

        # Barra grafica principale di avanzamento cattura/handshake.
        # Barra scanner ROUTER/CLIENT: SEMPRE blu, indipendente dal lavoro.
        style.configure(
            "ScanBlue.Horizontal.TProgressbar",
            thickness=16,
            troughcolor="#d9d9d9",
            background="#1565C0",
            bordercolor="#b8b8b8",
            lightcolor="#1565C0",
            darkcolor="#1565C0"
        )

        # Barra BLOCCO/CATTURA: cambia colore in base al comando attivo.
        style.configure(
            "Work.Horizontal.TProgressbar",
            thickness=16,
            troughcolor="#d9d9d9",
            background="#1565C0",
            bordercolor="#b8b8b8",
            lightcolor="#1565C0",
            darkcolor="#1565C0"
        )
        top = ttk.Frame(self.root, padding=(8,3))
        top.pack(fill="x")


        # Pulsante ESCI in alto a destra.
        self.exit_button = tk.Button(
            self.root,
            text="ESCI",
            command=self._shutdown_app,
            font=("TkDefaultFont", 9, "bold"),
            bg="#b71c1c",
            fg="white",
            activebackground="#d32f2f",
            activeforeground="white",
            relief="solid",
            borderwidth=1,
            highlightthickness=1,
            highlightbackground="#37474F",
            highlightcolor="#37474F",
            padx=9,
            pady=3,
            cursor="hand2"
        )
        self.exit_button.place(relx=1.0, x=-14, y=8, anchor="ne")
        self.exit_button.lift()

        # Pulsanti visibili + / - per regolare SOLO l'altezza della GUI.
        # La larghezza della finestra non viene mai modificata.
        self.gui_plus_button = tk.Button(
            self.root,
            text="+",
            command=self._increase_gui_vertical_only,
            font=("TkDefaultFont", 11, "bold"),
            bg="#455A64",
            fg="white",
            activebackground="#607D8B",
            activeforeground="white",
            relief="flat",
            borderwidth=0,
            width=2,
            padx=1,
            pady=2,
            cursor="hand2"
        )
        self.gui_plus_button.place(relx=1.0, x=-76, y=8, anchor="ne")
        self.gui_plus_button.lift()

        self.gui_minus_button = tk.Button(
            self.root,
            text="-",
            command=self._reduce_gui_vertical_only,
            font=("TkDefaultFont", 11, "bold"),
            bg="#455A64",
            fg="white",
            activebackground="#607D8B",
            activeforeground="white",
            relief="flat",
            borderwidth=0,
            width=2,
            padx=1,
            pady=2,
            cursor="hand2"
        )
        self.gui_minus_button.place(relx=1.0, x=-106, y=8, anchor="ne")
        self.gui_minus_button.lift()

        # DEBUG in alto a destra, a sinistra dei pulsanti + / -.
        self.debug_top_button = tk.Button(
            self.root,
            text="DEBUG",
            command=self.open_command_debug,
            font=("TkDefaultFont", 9, "bold"),
            bg="#455A64",
            fg="white",
            activebackground="#607D8B",
            activeforeground="white",
            relief="flat",
            borderwidth=0,
            width=7,
            padx=3,
            pady=3,
            cursor="hand2"
        )
        self.debug_top_button.place(relx=1.0, x=-138, y=8, anchor="ne")
        self.debug_top_button.lift()

        # ESPORTA GRAFICO: pulsante grande a due righe. Il bordo sinistro parte
        # dalla stessa colonna del pulsante DEBUG e si estende verso destra.
        self.network_diagram_export_button = tk.Button(
            self.root,
            text=("EXPORT\nGRAPH" if getattr(self, "language", "it") == "en" else "ESPORTA\nGRAFICO"),
            command=self.export_network_diagram_svg,
            font=("TkDefaultFont", 9, "bold"),
            bg="#B8860B",
            fg="white",
            activebackground="#D4A017",
            activeforeground="white",
            relief="solid",
            borderwidth=1,
            highlightthickness=1,
            highlightbackground="#37474F",
            highlightcolor="#37474F",
            padx=8,
            pady=2,
            justify="center",
            cursor="hand2"
        )
        # DEBUG termina circa a x=-138; con larghezza esplicita il nuovo pulsante
        # parte dalla stessa colonna del DEBUG e occupa lo spazio libero sottostante.
        self.network_diagram_export_button.place(relx=1.0, x=-200, y=42, anchor="nw", width=186, height=48)
        self.network_diagram_export_button.lift()
        # I frame creati dopo possono coprire un widget place(): rialzalo anche
        # quando Tk ha terminato il layout iniziale.
        for _delay in (80, 220, 500):
            try:
                self.root.after(_delay, self.network_diagram_export_button.lift)
            except Exception:
                pass

        # Firma Cyborg sempre visibile in basso a sinistra.
        self.cyborg_label = tk.Label(
            self.root,
            text="Ver 2.1 © Cyborg",
            font=("TkDefaultFont", 10, "bold"),
            bg=self.root.cget("bg"),
            fg="#555555"
        )
        self.cyborg_label.place(
            x=10,
            rely=1.0,
            y=-2,
            anchor="sw"
        )
        self.cyborg_label.lift()

        # Grande riquadro AVVISO nella zona alta a destra, come nello schema.
        # Il testo è distribuito su più righe e centrato con carattere grande.
        self.monitor_chip_warning = tk.Label(
            self.root,
            text=(
                "IL SOFTWARE FUNZIONA ESCLUSIVAMENTE CON CIP WIFI CHE POSSONO "
                "ESSERE CONFIGURATI IN MODALITA' MONITORAGGIO"
            ),
            font=("TkDefaultFont", 9, "bold"),
            bg="#2E7D32",
            fg="white",
            relief="solid",
            borderwidth=0,
            highlightthickness=2,
            highlightbackground="#000000",
            highlightcolor="#000000",
            justify="center",
            anchor="center",
            wraplength=420,
            padx=2,
            pady=2
        )
        # L'avviso viene posizionato dinamicamente:
        # - accostato al lato sinistro del pulsante VERSIONE NOTTURNA/DIURNA;
        # - esteso verticalmente fino appena sopra ROUTER RILEVATI.
        self.monitor_chip_warning.lift()

        # INTERFACCIA WIFI a sinistra, centrata verticalmente tra
        # le righe ORIGINE e MONITOR MODE.
        iface_block = ttk.Frame(top)
        iface_block.grid(
            row=0, column=0, rowspan=2,
            padx=(0,12), pady=0, sticky="w"
        )

        ttk.Label(
            iface_block,
            text="INTERFACCIA WIFI",
            font=("TkDefaultFont", 14, "bold"),
            anchor="w"
        ).pack(fill="x", anchor="w", pady=(0,3))

        iface_line = ttk.Frame(iface_block)
        iface_line.pack(anchor="w", fill="x")

        # WLAN -> ORIGINE -> MONITOR MODE sulla stessa riga.
        # Tutti i widget sono figli reali dello stesso frame.
        self.iface_combo = ttk.Combobox(
            iface_line,
            textvariable=self.iface,
            width=20,
            state="readonly"
        )
        self.iface_combo.pack(side="left", anchor="w")
        self.iface_combo.bind("<<ComboboxSelected>>", self._on_iface_selected)

        self.iface_origin_label = tk.Label(
            iface_line,
            textvariable=self.iface_origin,
            font=("TkDefaultFont", 12, "bold"),
            anchor="w",
            bg=self.root.cget("bg"),
            fg="#000000",
            borderwidth=0,
            highlightthickness=0
        )
        self.iface_origin_label.pack(side="left", padx=(6,14))

        self.monitor_mode_label = tk.Label(
            iface_line,
            textvariable=self.monitor_mode_state,
            font=("TkDefaultFont", 12, "bold"),
            anchor="center",
            bg="#FF0000",
            fg="#FFFFFF",
            activeforeground="#FFFFFF",
            relief="solid",
            borderwidth=0,
            highlightthickness=2,
            highlightbackground="#000000",
            highlightcolor="#000000",
            padx=7,
            pady=2
        )
        self.monitor_mode_label.pack(side="left", padx=(0,8))

        ttk.Button(top, text="AGGIORNA INTERFACCIE WIFI", command=self.refresh_interfaces).grid(row=0, column=2, padx=5)
        ttk.Button(top, text="ATTIVA MONITOR MODE", command=self.enable_monitor_mode).grid(row=0, column=3, padx=5)
        self.scan_wifi_button = tk.Button(
            top,
            text="SCANSIONA RETI WIFI",
            command=self.scan_aps,
            bg="#006BFF",
            fg="white",
            activebackground="#0052CC",
            activeforeground="white",
            font=("TkDefaultFont", 10, "bold"),
            relief="raised",
            borderwidth=2,
            padx=12,
            pady=5,
            cursor="hand2"
        )
        self.scan_wifi_button.grid(row=0, column=4, padx=5)

        # Grande pulsante per passare dalla grafica diurna a quella notturna.
        style.configure(
            "ThemeToggle.TButton",
            font=("TkDefaultFont", 11, "bold"),
            padding=(12, 10),
            anchor="center"
        )
        style.configure(
            "ThemeToggleDayHover.TButton",
            font=("TkDefaultFont", 11, "bold"),
            padding=(12, 10),
            background="#343A40",
            foreground="#F2F2F2",
            anchor="center"
        )
        style.map(
            "ThemeToggleDayHover.TButton",
            background=[("active", "#343A40"), ("pressed", "#20252B")],
            foreground=[("active", "#F2F2F2"), ("pressed", "#FFFFFF")]
        )

        style.configure(
            "ThemeToggleNightHover.TButton",
            font=("TkDefaultFont", 11, "bold"),
            padding=(12, 10),
            background="#E0E0E0",
            foreground="#505050",
            anchor="center"
        )
        style.map(
            "ThemeToggleNightHover.TButton",
            background=[("active", "#E0E0E0"), ("pressed", "#BEBEBE")],
            foreground=[("active", "#505050"), ("pressed", "#404040")]
        )
        self.theme_toggle_button = ttk.Button(
            top,
            textvariable=self.theme_button_text,
            command=self.toggle_night_mode,
            style="ThemeToggle.TButton",
            width=18
        )
        self.theme_toggle_button.grid(
            row=0, column=5, rowspan=2,
            padx=(18,5), pady=(0,2), ipadx=2, ipady=4, sticky="nsew"
        )

        def _theme_toggle_enter(_event=None):
            try:
                hover_style = (
                    "ThemeToggleNightHover.TButton"
                    if getattr(self, "night_mode", False)
                    else "ThemeToggleDayHover.TButton"
                )
                self.theme_toggle_button.configure(style=hover_style)
            except Exception:
                pass

        def _theme_toggle_leave(_event=None):
            try:
                self.theme_toggle_button.configure(style="ThemeToggle.TButton")
            except Exception:
                pass

        self.theme_toggle_button.bind("<Enter>", _theme_toggle_enter)
        self.theme_toggle_button.bind("<Leave>", _theme_toggle_leave)


        apf = ttk.LabelFrame(self.root, text="ROUTER RILEVATI", padding=8, style="Bold.TLabelframe")
        self.router_frame = apf
        apf.pack(fill="both", padx=10, pady=1)

        def _position_export_graph_button():
            """Tiene ESPORTA GRAFICO appena sopra il bordo superiore di ROUTER RILEVATI."""
            try:
                self.root.update_idletasks()
                btn = getattr(self, "network_diagram_export_button", None)
                frame = getattr(self, "router_frame", None)
                if btn is None or frame is None or not btn.winfo_exists():
                    return
                root_y = int(self.root.winfo_rooty())
                frame_top = int(frame.winfo_rooty()) - root_y
                top_y = 42
                # Il fondo resta 3 px sopra il bordo del riquadro router.
                # Questo stesso riferimento viene usato anche dal banner superiore.
                bottom_target = frame_top - 3
                available = max(34, bottom_target - top_y)
                height = max(38, min(48, available))
                btn.place_configure(relx=1.0, x=-200, y=top_y, anchor="nw", width=186, height=height)
                btn.lift()
            except Exception:
                pass

        self._position_export_graph_button = _position_export_graph_button
        for _delay in (100, 260, 520):
            try:
                self.root.after(_delay, _position_export_graph_button)
            except Exception:
                pass

        def _position_monitor_warning():
            try:
                self.root.update_idletasks()

                warning = getattr(self, "monitor_chip_warning", None)
                theme = getattr(self, "theme_toggle_button", None)
                debug_btn = getattr(self, "debug_top_button", None)
                frame = getattr(self, "router_frame", None)

                if warning is None or theme is None:
                    return

                root_x = int(self.root.winfo_rootx())
                root_y = int(self.root.winfo_rooty())

                theme_left = int(theme.winfo_rootx()) - root_x
                theme_top = int(theme.winfo_rooty()) - root_y
                theme_right = theme_left + int(theme.winfo_width())

                left = theme_right + 6

                if debug_btn is not None and debug_btn.winfo_exists():
                    right_limit = int(debug_btn.winfo_rootx()) - root_x - 10
                else:
                    right_limit = int(self.root.winfo_width()) - 100

                available_width = max(180, right_limit - left)
                width = available_width

                # Il bordo SUPERIORE del banner VERDE / BLU / ROSSO viene
                # allineato esattamente al bordo superiore del pulsante
                # VERSIONE NOTTURNA / DIURNA. Il bordo inferiore resta appena
                # sopra la tabella ROUTER RILEVATI, come ESPORTA GRAFICO.
                if frame is not None and frame.winfo_exists():
                    frame_top = int(frame.winfo_rooty()) - root_y
                    # Estende il riquadro VERDE / ROSSO / BLU di 5 px
                    # verso il basso, lasciando invariato il bordo superiore.
                    bottom_target = frame_top + 2
                else:
                    bottom_target = theme_top + max(52, int(theme.winfo_height()))

                top = theme_top
                height = max(42, bottom_target - top)

                # Durante il cambio tema mantiene la stessa geometria calcolata
                # dalla posizione reale della tabella router.
                self._warning_stable_geometry = (left, top, width, height)

                # La funzione di posizionamento deve modificare SOLO la geometria.
                # Il font viene deciso esclusivamente da _set_operation_mode_banner:
                # 6 pt per l'avviso verde, 18 pt per ATTIVA/PASSIVA.
                # In precedenza questo blocco forzava temporaneamente 10 pt durante
                # il cambio tema, causando il visibile effetto piccolo/grande.
                warning.configure(
                    wraplength=max(170, width - 12),
                    padx=4,
                    pady=2,
                    justify="center",
                    anchor="center"
                )

                warning.place(
                    x=left,
                    y=top,
                    width=width,
                    height=height,
                    anchor="nw"
                )
                warning.lift()
                try:
                    if hasattr(self, "_position_export_graph_button"):
                        self._position_export_graph_button()
                    else:
                        self.network_diagram_export_button.lift()
                except Exception:
                    pass
            except Exception:
                pass

        self._position_monitor_warning = _position_monitor_warning
        self.root.after(120, _position_monitor_warning)
        self.root.after(450, _position_monitor_warning)
        try:
            self.root.protocol("WM_DELETE_WINDOW", self._shutdown_app)
        except Exception:
            pass

        ap_progress_row = ttk.Frame(apf)
        ap_progress_row.pack(fill="x", pady=(0,1))

        self.router_count = tk.StringVar(value="Numero: 0")
        ttk.Label(
            ap_progress_row,
            textvariable=self.router_count,
            font=("TkDefaultFont", 14)
        ).pack(side="left", padx=(0,10))

        self.stop_ap_scan_button = ttk.Button(
            ap_progress_row,
            text="STOP RICERCA",
            command=self.stop_ap_scan,
            state="disabled"
        )
        self.stop_ap_scan_button.pack(side="left", padx=(0,10))

        ttk.Label(
            ap_progress_row,
            text="Rilevamento Routers WIFI",
            font=("TkDefaultFont", 12, "bold")
        ).pack(side="left", padx=(0,10))

        ttk.Progressbar(
            ap_progress_row,
            variable=self.ap_scan_progress,
            maximum=100,
            length=300,
            mode="determinate",
            style="ScanBlue.Horizontal.TProgressbar"
        ).pack(side="left", padx=(0,5), fill="x", expand=True)

        ttk.Label(
            ap_progress_row,
            textvariable=self.ap_scan_progress_text,
            width=6,
            anchor="e"
        ).pack(side="left")

        # Ordine corrente:
        # BSSID | CANALE | POTENZA | ESSID | BANDA | CLIENTI | PACCHETTI | CRIPTAZIONE
        cols = ("bssid","ch","pwr","essid","band","clients","packets","enc")
        ap_tree_holder = ttk.Frame(apf)
        ap_tree_holder.pack(fill="both", expand=True)
        ap_tree_holder.columnconfigure(0, weight=1)
        ap_tree_holder.rowconfigure(0, weight=1)

        self.ap_tree = ttk.Treeview(
            ap_tree_holder,
            columns=cols,
            show="headings",
            height=5,
            style="Scanner.Treeview"
        )
        headings = {
            "bssid":"BSSID",
            "ch":"CANALE",
            "band":"BANDA",
            "clients":"CLIENTI",
            "packets":"PACCHETTI",
            "enc":"CRIPTAZIONE",
            "pwr":"POTENZA",
            "essid":"ESSID"
        }
        for c,w in [
            ("bssid",190),("ch",70),("pwr",125),("essid",310),
            ("band",110),("clients",115),("packets",135),("enc",105)
        ]:
            if c in ("band", "packets", "pwr", "clients"):
                self.ap_tree.heading(
                    c,
                    text=headings[c],
                    anchor="center",
                    command=lambda col=c: self._sort_ap_tree_by_heading(col)
                )
            else:
                self.ap_tree.heading(c, text=headings[c], anchor="center")
            self.ap_tree.column(c, width=w, anchor="center")
        self.ap_tree.grid(row=0, column=0, sticky="nsew")
        ap_y = ttk.Scrollbar(ap_tree_holder, orient="vertical", command=self.ap_tree.yview)
        ap_y.grid(row=0, column=1, sticky="ns")
        self.ap_tree.configure(yscrollcommand=ap_y.set)
        self.ap_tree.bind("<<TreeviewSelect>>", self.on_ap_select)

        client_bar = ttk.Frame(self.root, padding=(8,2))
        client_bar.pack(fill="x")

        # Layout dinamico: la scritta ESSID/BSSID occupa lo spazio necessario
        # e la barra client usa automaticamente tutto lo spazio residuo.
        # In questo modo, se il nome è lungo la barra si accorcia; se è corto
        # la barra si allunga, mantenendo sempre lo stesso margine destro
        # della barra di ricerca router.

        self.scan_client_button = tk.Button(
            client_bar,
            text="SCANSIONA CLIENT DELL'AP SELEZIONATO",
            command=self.scan_clients,
            bg="#006BFF",
            fg="white",
            activebackground="#0052CC",
            activeforeground="white",
            font=("TkDefaultFont", 10, "bold"),
            relief="raised",
            borderwidth=2,
            padx=12,
            pady=5,
            cursor="hand2"
        )
        self.scan_client_button.grid(row=0, column=0, sticky="w")

        ttk.Label(
            client_bar,
            textvariable=self.client_search_caption,
            font=("TkDefaultFont", 12, "bold")
        ).grid(row=0, column=1, sticky="w", padx=(15,5))



        cf = ttk.LabelFrame(self.root, text="DISPOSITIVI CLIENT WIFI", padding=(8,2,8,8), style="Bold.TLabelframe")
        cf.pack(fill="both", padx=10, pady=1)
        client_count_row = ttk.Frame(cf)
        client_count_row.pack(fill="x", pady=(0,0))

        ttk.Label(
            client_count_row,
            textvariable=self.client_count,
            font=("TkDefaultFont", 12),
            anchor="w"
        ).pack(side="left", padx=(0,10))

        self.stop_client_scan_button = ttk.Button(
            client_count_row,
            text="STOP RICERCA",
            command=self.stop_client_scan,
            state="disabled"
        )
        self.stop_client_scan_button.pack(side="left", padx=(0,10))
        self.client_progressbar = ttk.Progressbar(
            client_count_row,
            variable=self.client_scan_progress,
            maximum=100,
            mode="determinate",
            style="ScanBlue.Horizontal.TProgressbar",
            length=300
        )
        self.client_progressbar.pack(
            side="left",
            padx=(0,5),
            fill="x",
            expand=True
        )

        ttk.Label(
            client_count_row,
            textvariable=self.client_scan_progress_text,
            width=6,
            anchor="e"
        ).pack(side="left")

        ccols = ("station","resolved","vendor","pwr","packets","probes","source")
        client_tree_holder = ttk.Frame(cf)
        client_tree_holder.pack(fill="both", expand=True)
        client_tree_holder.columnconfigure(0, weight=1)
        client_tree_holder.rowconfigure(0, weight=1)

        self.client_tree = ttk.Treeview(
            client_tree_holder,
            columns=ccols,
            show="headings",
            height=3,
            style="Scanner.Treeview"
        )
        client_headings = {
            "station":"STAZIONI",
            "resolved":"DISPOSITIVO",
            "vendor":"VENDITORE",
            "pwr":"POTENZA",
            "packets":"PACCHETTI",
            "probes":"SONDA",
            "source":"PROVENIENZA"
        }
        for c,w in [
            ("station",210),("resolved",235),("vendor",235),
            ("pwr",120),("packets",135),("probes",210),("source",360)
        ]:
            self.client_tree.heading(
                c,
                text=client_headings[c],
                anchor="center",
                command=lambda col=c: self._sort_client_tree_by_heading(col)
            )
            self.client_tree.column(c, width=w, anchor="center")
        self.client_tree.grid(row=0, column=0, sticky="nsew")
        client_y = ttk.Scrollbar(client_tree_holder, orient="vertical", command=self.client_tree.yview)
        client_y.grid(row=0, column=1, sticky="ns")
        self.client_tree.configure(yscrollcommand=client_y.set)
        self.client_tree.bind("<<TreeviewSelect>>", self.on_client_select)

        # ==========================================================
        # AREA OPERATIVA PRINCIPALE - layout ispirato allo schema
        # disegnato dall'utente:
        #   SINISTRA : DISPOSITIVI LAN sopra, BLOCCO/CATTURA sotto
        #   DESTRA   : HANDSHAKE + MACS CATTURATI sopra,
        #              POSSIBILI TELECAMERE RILEVATE sotto
        # ==========================================================
        analysis_area = ttk.Frame(self.root, padding=(10,1,10,2))
        analysis_area.pack(fill="both", expand=True)
        self.analysis_area = analysis_area

        # La parte destra e' stata allargata: in questo modo il riquadro
        # POSSIBILI TELECAMERE RILEVATE parte molto piu' a sinistra, arrivando
        # visivamente vicino alla zona DURATA del pannello DISTURBO.
        # Il pannello operativo sinistro deve avere spazio reale sufficiente per
        # mostrare CATTURA PASSIVA e DISTURBO secondo lo schema richiesto.
        analysis_area.columnconfigure(0, weight=48, uniform="main", minsize=max(600, int(self.screen_width * 0.44)))
        analysis_area.columnconfigure(1, weight=52, uniform="main", minsize=max(560, int(self.screen_width * 0.46)))
        analysis_area.rowconfigure(0, weight=1)

        left_stack = ttk.Frame(analysis_area)
        left_stack.grid(row=0, column=0, sticky="nsew", padx=(0,5))
        left_stack.columnconfigure(0, weight=1)
        left_stack.rowconfigure(0, weight=1)
        left_stack.rowconfigure(1, weight=1)

        right_stack = ttk.Frame(analysis_area)
        right_stack.grid(row=0, column=1, sticky="nsew", padx=(5,0))
        right_stack.columnconfigure(0, weight=1)
        # Parte alta piu' bassa, tabella telecamere piu' grande.
        right_stack.rowconfigure(0, weight=1)
        right_stack.rowconfigure(1, weight=3)

        # ----------------------------------------------------------
        # SINISTRA / ALTO - DISPOSITIVI LAN
        # ----------------------------------------------------------
        lanvf = ttk.LabelFrame(
            left_stack,
            text="POSSIBILI DISPOSITIVI LAN",
            padding=(8,2,8,8),
            style="Bold.TLabelframe"
        )
        lanvf.grid(row=0, column=0, sticky="nsew", pady=(0,4))
        lanvf.columnconfigure(0, weight=1)
        lanvf.rowconfigure(1, weight=1)

        ttk.Label(
            lanvf,
            textvariable=self.probable_lan_vendor_count,
            font=("TkDefaultFont", 12)
        ).grid(row=0, column=0, sticky="w", pady=(0,1))


        lvcols=("vendor","role","level","score","macs","source")
        self.lan_vendor_tree=ttk.Treeview(
            lanvf,
            columns=lvcols,
            show="headings",
            height=4,
            style="Scanner.Treeview"
        )
        lan_headings = {
            "vendor": "VENDOR",
            "macs": "MAC ADDRESSES",
            "score": "SC",
            "level": "LIKELIHOOD",
            "role": "ROLE",
            "source": "SOURCE"
        }
        for c,w in [
            ("vendor",115),
            ("role",90),
            ("level",140),
            ("score",245),
            ("macs",115),
            ("source",605)
        ]:
            self.lan_vendor_tree.heading(c,text=lan_headings[c],anchor="center")
            self.lan_vendor_tree.column(c,width=w,anchor="center",stretch=True)
        self.lan_vendor_tree.grid(row=1, column=0, sticky="nsew")
        lan_y = ttk.Scrollbar(lanvf, orient="vertical", command=self.lan_vendor_tree.yview)
        lan_y.grid(row=1, column=1, sticky="ns")
        self.lan_vendor_tree.configure(yscrollcommand=lan_y.set)
        self.lan_vendor_tree.bind("<ButtonRelease-1>", self._on_lan_row_click)
        self._lan_score_overlay_labels = []
        self.lan_vendor_tree.bind(
            "<Configure>",
            lambda _e: self._refresh_lan_score_font_overlay(),
            add="+"
        )
        self.lan_vendor_tree.bind(
            "<<TreeviewSelect>>",
            lambda _e: self._refresh_lan_score_font_overlay(),
            add="+"
        )
        self.root.after(300, self._refresh_lan_score_font_overlay)

        # ----------------------------------------------------------
        # SINISTRA / BASSO - BLOCCO/CATTURA + barra avanzamento
        # ----------------------------------------------------------
        capture_section = ttk.Frame(left_stack)
        capture_section.grid(row=1, column=0, sticky="nsew", pady=(4,0))
        capture_section.columnconfigure(0, weight=1)
        capture_section.rowconfigure(1, weight=1)

        capture_header = ttk.Frame(capture_section)
        capture_header.grid(row=0, column=0, sticky="ew", pady=(0,3))
        capture_header.columnconfigure(1, weight=1)

        ttk.Label(
            capture_header,
            text="BLOCCO/CATTURA",
            font=("TkDefaultFont", 10, "bold")
        ).grid(row=0, column=0, sticky="w")


        progress_holder = ttk.Frame(capture_header)
        progress_holder.grid(row=0, column=1, sticky="ew", padx=(10,5))

        self.main_capture_progress = ttk.Progressbar(
            progress_holder,
            variable=self.progress_value,
            maximum=100,
            mode="determinate",
            orient="horizontal",
            style="Work.Horizontal.TProgressbar"
        )
        self.main_capture_progress.pack(fill="x", expand=True, ipady=2)

        ttk.Label(
            capture_header,
            textvariable=self.progress_text,
            width=5,
            anchor="e",
            font=("TkDefaultFont", 9, "bold")
        ).grid(row=0, column=2, sticky="e")

        capture_box = ttk.LabelFrame(
            capture_section,
            text="",
            padding=(6,4),
            style="Bold.TLabelframe"
        )
        capture_box.grid(row=1, column=0, sticky="nsew")
        capture_box.columnconfigure(0, weight=0, minsize=205)
        capture_box.columnconfigure(1, weight=1, minsize=430)
        capture_box.rowconfigure(0, weight=1)

        # --- colonna sinistra compatta: BSSID / CLIENT / CANALE / BLOCCO ---
        left_col = ttk.Frame(capture_box)
        left_col.grid(row=0, column=0, sticky="nsw", padx=(0,6))

        ttk.Label(left_col,text="BSSID:").grid(row=0,column=0,sticky="w",padx=(0,5),pady=1)
        ttk.Entry(left_col,textvariable=self.bssid,width=18).grid(row=0,column=1,sticky="w",pady=1)
        ttk.Label(left_col,text="CLIENT:").grid(row=1,column=0,sticky="w",padx=(0,5),pady=1)
        ttk.Entry(left_col,textvariable=self.client,width=18).grid(row=1,column=1,sticky="w",pady=1)
        ttk.Label(left_col,text="CANALE:").grid(row=2,column=0,sticky="w",padx=(0,5),pady=1)
        ttk.Entry(left_col,textvariable=self.channel,width=8).grid(row=2,column=1,sticky="w",pady=1)


        # Titolo area BLOCCO/BLOCK: leggermente più grande e in grassetto.
        self.style.configure("BlockArea.TLabelframe.Label", font=("TkDefaultFont", 11, "bold"))
        block_panel = ttk.LabelFrame(left_col,style="BlockArea.TLabelframe",text="BLOCCO",padding=(3,1))
        self.block_panel = block_panel
        block_panel.grid(row=3,column=0,columnspan=2,sticky="ew",pady=(3,1))
        block_panel.columnconfigure(1, weight=1)

        ttk.Label(block_panel,text="ROUTER",font=("TkDefaultFont",9,"bold")).grid(row=0,column=0,sticky="w",padx=(0,4),pady=(0,1))
        self.block_router_entry = ttk.Entry(block_panel,textvariable=self.block_router_value,state="readonly",width=11)
        self.block_router_entry.grid(row=0,column=1,columnspan=2,sticky="ew",pady=(0,1))
        self.aireplay_ng_router_start_button = tk.Button(block_panel,text="AVVIA",width=6,command=self.start_aireplay_ng_router,relief="raised",borderwidth=2,cursor="hand2")
        self.aireplay_ng_router_start_button.grid(row=1,column=0,sticky="w",padx=(0,4),pady=(0,2))
        self.aireplay_ng_router_stop_button = tk.Button(block_panel,text="FERMA",width=6,command=self.stop_aireplay_ng_router,relief="raised",borderwidth=2,cursor="hand2")
        self.aireplay_ng_router_stop_button.grid(row=1,column=1,sticky="w",pady=(0,2))

        ttk.Label(block_panel,text="CLIENT",font=("TkDefaultFont",9,"bold")).grid(row=2,column=0,sticky="w",padx=(0,4),pady=(0,1))
        self.block_client_entry = ttk.Entry(block_panel,textvariable=self.block_client_value,state="readonly",width=11)
        self.block_client_entry.grid(row=2,column=1,columnspan=2,sticky="ew",pady=(0,1))
        self.aireplay_ng_client_start_button = tk.Button(block_panel,text="AVVIA",width=6,command=self.start_aireplay_ng_client,relief="raised",borderwidth=2,cursor="hand2")
        self.aireplay_ng_client_start_button.grid(row=3,column=0,sticky="w",padx=(0,4))
        self.aireplay_ng_client_stop_button = tk.Button(block_panel,text="FERMA",width=6,command=self.stop_aireplay_ng_client,relief="raised",borderwidth=2,cursor="hand2")
        self.aireplay_ng_client_stop_button.grid(row=3,column=1,sticky="w")

        left_col.columnconfigure(0,minsize=72)

        # --- colonna destra del riquadro cattura: CATTURA PASSIVA + DISTURBO ---
        controls_col = ttk.Frame(capture_box)
        controls_col.grid(row=0,column=1,sticky="nsew",padx=(3,0))
        controls_col.columnconfigure(0, weight=1)

        # ==========================================================
        # NUOVO LAYOUT FORZATO CATTURA / DISTURBO - wifi_401
        # ==========================================================

        passive_title_label = ttk.Label(
            controls_col,
            textvariable=self.passive_box_title,
            font=("TkDefaultFont",10,"bold")
        )
        passive_box = ttk.LabelFrame(
            controls_col,
            labelwidget=passive_title_label,
            padding=(7,6)
        )
        passive_box.grid(row=0,column=0,sticky="ew",pady=(0,7))
        passive_box.columnconfigure(0,weight=1)

        # -------------------------
        # CATTURA PASSIVA - 1 RIGA
        # -------------------------
        passive_line = ttk.Frame(passive_box)
        passive_line.grid(row=0,column=0,sticky="w")

        self.start_capture_button = tk.Button(
            passive_line,
            text="AVVIA",
            width=9,
            command=self.start_capture,
            relief="raised",
            borderwidth=2,
            cursor="hand2"
        )
        self.start_capture_button.pack(side="left",padx=(0,8),pady=3)

        self.stop_capture_button = tk.Button(
            passive_line,
            text="FERMA",
            width=9,
            command=self.stop_capture,
            relief="raised",
            borderwidth=2,
            cursor="hand2"
        )
        self.stop_capture_button.pack(side="left",padx=(0,18),pady=3)

        ttk.Label(
            passive_line,
            text="DURATA (sec):",
            font=("TkDefaultFont",9,"bold")
        ).pack(side="left",padx=(0,5))

        ttk.Entry(
            passive_line,
            textvariable=self.capture_duration,
            width=8
        ).pack(side="left",padx=(0,18))

        self.export_capture_button_text = tk.StringVar(value="ESPORTA")
        self.export_capture_button = ttk.Button(
            passive_line,
            textvariable=self.export_capture_button_text,
            command=self.export_capture_file,
            state="disabled"
        )
        self.export_capture_button.pack(side="left")

        # -------------------------
        # DISTURBO - 3 COLONNE REALI
        # -------------------------
        disturb_title_label = ttk.Label(
            controls_col,
            textvariable=self.disturb_box_title,
            font=("TkDefaultFont",10,"bold")
        )
        disturb_box = ttk.LabelFrame(
            controls_col,
            labelwidget=disturb_title_label,
            padding=(7,6)
        )
        disturb_box.grid(row=1,column=0,sticky="ew")
        disturb_box.columnconfigure(0,weight=0,minsize=230)
        disturb_box.columnconfigure(1,weight=0,minsize=145)
        disturb_box.columnconfigure(2,weight=1,minsize=190)

        # SINISTRA: AVVIA + FERMA, flag sotto
        left_disturb = ttk.Frame(disturb_box)
        left_disturb.grid(row=0,column=0,sticky="nw",padx=(0,12))

        buttons_line = ttk.Frame(left_disturb)
        buttons_line.pack(anchor="w")

        self.start_disturb_button = tk.Button(
            buttons_line,
            text="AVVIA",
            width=9,
            command=self.start_diegi_external,
            relief="raised",
            borderwidth=2,
            cursor="hand2"
        )
        self.start_disturb_button.pack(side="left",padx=(0,8),pady=(1,4))

        self.stop_disturb_button = tk.Button(
            buttons_line,
            text="FERMA",
            width=9,
            command=self.stop_diegi_external,
            relief="raised",
            borderwidth=2,
            cursor="hand2"
        )
        self.stop_disturb_button.pack(side="left",pady=(1,4))

        handshake_check = tk.Checkbutton(
            left_disturb,
            text="TERMINA SE TROVI HANDSHAKE",
            variable=self.stop_on_handshake,
            command=self._sync_stop_on_handshake_flag,
            font=("TkDefaultFont",8,"bold"),
            indicatoron=True,
            borderwidth=0,
            relief="flat",
            offrelief="flat",
            overrelief="flat",
            highlightthickness=0,
            selectcolor="white",
            padx=1,
            pady=0,
            anchor="w"
        )
        handshake_check.pack(anchor="w",pady=(4,0))

        # CENTRO: DURATA / PAUSA / RIP. verticali
        center_disturb = ttk.Frame(disturb_box)
        center_disturb.grid(row=0,column=1,sticky="n",padx=(0,12))

        for rr, (labtxt, var) in enumerate((
            ("DURATA (sec):", self.disturb_duration),
            ("PAUSA (sec):", self.pause_seconds),
            ("RIP.:", self.repetitions),
        )):
            ttk.Label(
                center_disturb,
                text=labtxt,
                font=("TkDefaultFont",9,"bold")
            ).grid(row=rr,column=0,sticky="e",padx=(0,5),pady=2)

            ttk.Entry(
                center_disturb,
                textvariable=var,
                width=7
            ).grid(row=rr,column=1,sticky="w",pady=2)

        # ESPORTA HANDSHAKE subito dopo il campo PAUSA, sulla stessa riga.
        self.export_handshake_button = ttk.Button(
            center_disturb,
            text="ESPORTA HANDSHAKE",
            command=self.export_capture_file,
            state="disabled"
        )
        self.export_handshake_button.grid(
            row=1,column=2,sticky="w",padx=(14,0),pady=2
        )

        # ----------------------------------------------------------
        # DESTRA / ALTO - HANDSHAKE piccolo + MACS CATTURATI
        # ----------------------------------------------------------
        upper_right = ttk.Frame(right_stack)
        upper_right.grid(row=0,column=0,sticky="nsew",pady=(0,4))
        upper_right.columnconfigure(0,weight=0,minsize=145)
        upper_right.columnconfigure(1,weight=1)
        upper_right.rowconfigure(0,weight=1)

        hs_box = ttk.LabelFrame(upper_right,text="HANDSHAKE",padding=(4,2))
        hs_box.grid(row=0,column=0,sticky="nsew",padx=(0,4))
        hs_box.columnconfigure(1,weight=1)

        # HANDSHAKE: visualizza M1/M2/M3/M4 e sotto lo stato ASSENTE/TROVATO.
        self.handshake_part_widgets=[]
        for row, (label, var) in enumerate((
            ("M1:", self.handshake_m1),
            ("M2:", self.handshake_m2),
            ("M3:", self.handshake_m3),
            ("M4:", self.handshake_m4),
        )):
            lab = ttk.Label(
                hs_box, text=label,
                font=("TkDefaultFont",10,"bold"),
                anchor="w"
            )
            lab.grid(row=row,column=0,sticky="w",padx=(3,5),pady=1)
            val = ttk.Label(
                hs_box, textvariable=var,
                font=("TkDefaultFont",9),
                anchor="w"
            )
            val.grid(row=row,column=1,sticky="ew",padx=(0,3),pady=1)
            self.handshake_part_widgets.extend((lab,val))

        self.handshake_separator = ttk.Separator(hs_box, orient="horizontal")
        self.handshake_separator.grid(
            row=4,column=0,columnspan=2,sticky="ew",padx=3,pady=(3,2)
        )
        self.handshake_header_label=None
        self.handshake_state_label=ttk.Label(
            hs_box,
            textvariable=self.handshake_state,
            font=("TkDefaultFont",15,"bold"),
            anchor="center",
            justify="center"
        )
        self.handshake_state_label.grid(
            row=5,column=0,columnspan=2,sticky="ew",padx=4,pady=(2,4)
        )
        hs_box.columnconfigure(1,weight=1)

        rf = ttk.LabelFrame(upper_right,text="MACS CATTURATI",padding=3)
        rf.grid(row=0,column=1,sticky="nsew",padx=(4,0))
        rf.columnconfigure(0,weight=1)
        rf.rowconfigure(0,weight=1)

        rcols=("mac","vendor","class","evidence","notes","source")
        self.res_tree=ttk.Treeview(rf,columns=rcols,show="headings",height=3)
        res_headings_it={
            "mac":"MAC",
            "vendor":"VENDITORE",
            "class":"CLASSE",
            "evidence":"PROVA",
            "notes":"NOTE",
            "source":"PROVENIENZA"
        }
        for c,w in [("mac",115),("vendor",115),("class",105),("evidence",140),("notes",165),("source",360)]:
            self.res_tree.heading(c,text=res_headings_it[c],anchor="center")
            self.res_tree.column(c,width=w,anchor="center",stretch=True)
        self.res_tree.grid(row=0,column=0,sticky="nsew")

        res_y = ttk.Scrollbar(rf,orient="vertical",command=self.res_tree.yview)
        res_y.grid(row=0,column=1,sticky="ns")
        self.res_tree.configure(yscrollcommand=res_y.set)

        # ----------------------------------------------------------
        # DESTRA / BASSO - POSSIBILI TELECAMERE RILEVATE
        # ----------------------------------------------------------
        camera_box = ttk.LabelFrame(right_stack,text="POSSIBILI TELECAMERE RILEVATE",padding=3,style="CameraTitle.TLabelframe")
        camera_box.grid(row=1,column=0,sticky="nsew",pady=(4,0))
        camera_box.columnconfigure(0,weight=1)
        camera_box.rowconfigure(0,weight=0)
        camera_box.rowconfigure(1,weight=1)
        camera_box.rowconfigure(2,weight=0,minsize=38)
        camera_box.rowconfigure(3,weight=0,minsize=0)

        camera_cols=("mac","vendor","score","level","txrx","provenance","duration")

        # Font TELECAMERE: usa la dimensione massima ragionevole per lo schermo.
        # La scrollbar orizzontale permette di mantenere il testo grande senza
        # comprimere le colonne fino a renderle illeggibili.
        # Font compatto e adattato alle celle: privilegia la leggibilità completa
        # delle intestazioni e dei valori senza caratteri sovradimensionati.
        # Corpo più piccolo per evitare troncamenti, in particolare nella colonna VENDITORE.
        # Treeview applica il font per riga (non per singola colonna), quindi manteniamo
        # intestazioni leggibili ma valori più compatti.
        if self.screen_width >= 1800:
            camera_font_size = 10
            camera_heading_size = 9
        elif self.screen_width >= 1500:
            camera_font_size = 10
            camera_heading_size = 8
        elif self.screen_width >= 1200:
            camera_font_size = 9
            camera_heading_size = 8
        else:
            camera_font_size = 9
            camera_heading_size = 7

        style.configure(
            "Camera.Treeview",
            rowheight=max(23, camera_font_size + 13),
            font=("TkDefaultFont", camera_font_size)
        )
        style.configure(
            "Camera.Treeview.Heading",
            font=("TkDefaultFont", camera_heading_size, "bold")
        )
        self.camera_tree=ttk.Treeview(
            camera_box,columns=camera_cols,show="headings",height=5,style="Camera.Treeview"
        )
        camera_headings={
            "mac":"MAC","vendor":"VENDITORE","score":"SCORE","level":"PROBABILITA'",
            "txrx":"TX/RX","provenance":"PROVENIENZA","duration":"DURATA (sec)"
        }
        # Larghezze maggiorate: le intestazioni restano leggibili per intero.
        # Se la finestra è più stretta si usa la scrollbar orizzontale invece di
        # ridurre eccessivamente i caratteri.
        for c,w in [
            ("mac",145),("vendor",290),("score",75),("level",140),
            ("txrx",72),("provenance",115),("duration",95)
        ]:
            self.camera_tree.heading(c,text=camera_headings[c],anchor="center")
            self.camera_tree.column(c,width=w,minwidth=42,anchor="center",stretch=True)
        self.camera_tree.grid(row=1,column=0,sticky="nsew")

        # Riga azioni sempre visibile sotto la tabella telecamere.
        camera_action_row = ttk.Frame(camera_box)
        camera_action_row.grid(
            row=2, column=0, columnspan=2,
            sticky="ew",
            padx=(2,2),
            pady=(6,4)
        )

        # I pulsanti devono essere figli REALI di camera_action_row:
        # in questo modo Tk li visualizza correttamente e non dipendono
        # dal parametro grid(in_=...).
        self.camera_details_button = tk.Button(
            camera_action_row,
            text="DETTAGLI",
            command=self._camera_show_selected_detail,
            state="disabled",
            font=("TkDefaultFont", 10, "bold"),
            bg="#D9D9D9",
            fg="#202020",
            activebackground="#BDBDBD",
            activeforeground="#000000",
            disabledforeground="#888888",
            relief="raised",
            borderwidth=3,
            padx=18,
            pady=4,
            cursor="hand2"
        )

        self.camera_block_action_button = tk.Button(
            camera_action_row,
            text="BLOCCA DISPOSITIVO SELEZIONATO",
            command=self._camera_block_selected_client,
            state="disabled",
            font=("TkDefaultFont", 10, "bold"),
            bg="#D9D9D9",
            fg="#202020",
            activebackground="#BDBDBD",
            activeforeground="#000000",
            disabledforeground="#888888",
            relief="raised",
            borderwidth=3,
            padx=14,
            pady=4,
            cursor="hand2"
        )
        self.camera_block_action_button.pack(side="right", padx=(0,8))
        self.camera_details_button.pack(side="right")

        ttk.Label(
            camera_box,
            textvariable=self.camera_number_text,
            font=("TkDefaultFont", 16, "bold"),
            anchor="w"
        ).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0,3))

        cam_y = ttk.Scrollbar(camera_box,orient="vertical",command=self.camera_tree.yview)
        cam_y.grid(row=1,column=1,sticky="ns")
        self.camera_tree.configure(yscrollcommand=cam_y.set)
        self.camera_tree.bind("<ButtonRelease-1>", self._on_camera_row_click, add="+")
        self.camera_tree.bind("<<TreeviewSelect>>", lambda _e: self._camera_selection_changed(), add="+")

        # Fascia inferiore rimossa dalla GUI.
        # Manteniamo un widget Text non visualizzato perché il programma usa
        # ancora self.log internamente per i messaggi diagnostici.
        self.log = tk.Text(self.root, height=1)
        # Colori scanner fissati DOPO il recoloring generale del tema.
        # Notte: conserva i colori notturni correnti.
        # Giorno: ripristina sempre il blu elettrico.
        try:
            if not getattr(self, "night_mode", False):
                for _btn in (self.scan_wifi_button, self.scan_client_button):
                    _btn.configure(
                        bg="#006BFF",
                        fg="white",
                        activebackground="#0052CC",
                        activeforeground="white"
                    )
        except Exception:
            pass
        self._apply_scanner_button_colors()
        self._refresh_cyborg_label()
        self._refresh_camera_block_button_theme()


    def _button_base_colors(self, button_name):
        """Colori normali dei pulsanti, coerenti con tema giorno/notte."""
        if button_name in ("scan_wifi_button", "scan_client_button"):
            if getattr(self, "night_mode", False):
                return ("#1E90FF", "#DCE8F3", "#061E39")
            return ("#006BFF", "#FFFFFF", "#0052CC")

        if getattr(self, "night_mode", False):
            return ("#111111", "#d6d8dc", "#222222")
        return ("#e7e7e7", "#000000", "#f4f4f4")

    def _start_button_blink(self, button_name):
        """Mantiene il lampeggio attivo finché non viene fermato esplicitamente."""
        # Cancella un eventuale timer precedente senza disattivare il nuovo ciclo.
        old_aid = self._button_blink_after.pop(button_name, None)
        if old_aid is not None:
            try:
                self.root.after_cancel(old_aid)
            except Exception:
                pass

        btn = getattr(self, button_name, None)
        if btn is None:
            return

        self._button_blink_running[button_name] = True
        self._button_blink_phase[button_name] = False

        def tick():
            # Solo _stop_button_blink() può terminare definitivamente il ciclo.
            if not self._button_blink_running.get(button_name, False):
                return

            btn_now = getattr(self, button_name, None)
            if btn_now is None:
                # Il widget può non essere disponibile per un singolo ridisegno:
                # non interrompere il lampeggio, riprova.
                try:
                    self._button_blink_after[button_name] = self.root.after(450, tick)
                except Exception:
                    pass
                return

            try:
                exists = bool(btn_now.winfo_exists())
            except Exception:
                exists = False

            if exists:
                phase = not self._button_blink_phase.get(button_name, False)
                self._button_blink_phase[button_name] = phase

                base_bg, base_fg, active_bg = self._button_base_colors(button_name)
                dark_mode = bool(getattr(self, "night_mode", False))

                if button_name in ("scan_wifi_button", "scan_client_button"):
                    blink_bg = "#7A6200" if dark_mode else "#FFC107"
                    blink_fg = "#F1E8B8" if dark_mode else "#000000"
                elif button_name == "start_capture_button":
                    blink_bg = "#1E90FF" if dark_mode else "#1565C0"
                    blink_fg = "#DCE8F3" if dark_mode else "#FFFFFF"
                else:
                    blink_bg = "#741A1A" if dark_mode else "#FF0000"
                    blink_fg = "#F3DCDC" if dark_mode else "#FFFFFF"

                try:
                    btn_now.configure(
                        bg=(blink_bg if phase else base_bg),
                        fg=(blink_fg if phase else base_fg),
                        activebackground=(blink_bg if phase else active_bg),
                        activeforeground=(blink_fg if phase else base_fg)
                    )
                except Exception:
                    # Un ridisegno/tema non deve mai far morire il timer.
                    pass

            # Pianifica SEMPRE il tick successivo finché running=True.
            if self._button_blink_running.get(button_name, False):
                try:
                    self._button_blink_after[button_name] = self.root.after(450, tick)
                except Exception:
                    pass

        try:
            self._button_blink_after[button_name] = self.root.after(0, tick)
        except Exception:
            pass

    def _stop_button_blink(self, button_name, restore=True):
        """Ferma definitivamente il lampeggio e ripristina il colore normale."""
        self._button_blink_running[button_name] = False

        aid = self._button_blink_after.pop(button_name, None)
        if aid is not None:
            try:
                self.root.after_cancel(aid)
            except Exception:
                pass

        self._button_blink_phase.pop(button_name, None)

        if not restore:
            return

        def apply():
            btn = getattr(self, button_name, None)
            if btn is None:
                return
            base_bg, base_fg, active_bg = self._button_base_colors(button_name)
            try:
                btn.configure(
                    bg=base_bg,
                    fg=base_fg,
                    activebackground=active_bg,
                    activeforeground=base_fg
                )
            except Exception:
                pass

        try:
            self.root.after(0, apply)
        except Exception:
            pass


    def _configure_plain_tk_widgets(self, night):
        """Aggiorna i widget Tk classici che non seguono gli stili ttk."""
        bg = "#000000" if night else "#f0f0f0"
        fg = "#d6d8dc" if night else "#000000"
        select_bg = "#39404a" if night else "#c3c3c3"

        def walk(widget):
            try:
                for child in widget.winfo_children():
                    cls = child.winfo_class()
                    try:
                        if cls in ("Checkbutton", "Radiobutton"):
                            child.configure(
                                background=bg,
                                foreground=fg,
                                activebackground=bg,
                                activeforeground=fg,
                                selectcolor=select_bg,
                                highlightbackground=bg
                            )
                        elif cls in ("Text", "Listbox"):
                            child.configure(
                                background=("#000000" if night else "white"),
                                foreground=fg,
                                insertbackground=fg,
                                selectbackground=select_bg
                            )
                    except Exception:
                        pass
                    walk(child)
            except Exception:
                pass

        walk(self.root)

        # I due pulsanti di scansione devono restare BLU sia in modalità
        # diurna sia in modalità notturna. Sono tk.Button classici proprio
        # per evitare che il tema ttk sovrascriva il colore.
        for _btn_name in (
            "scan_wifi_button", "scan_client_button",
             
            "start_capture_button", "start_disturb_button"
        ):
            if _btn_name in getattr(self, "_button_blink_after", {}):
                continue
            self._stop_button_blink(_btn_name, restore=True)

        # ESPORTA GRAFICO segue esplicitamente la modalita' giorno/notte.
        _export_btn = getattr(self, "network_diagram_export_button", None)
        if _export_btn is not None:
            try:
                if night:
                    _export_btn.configure(
                        bg="#101820", fg="#EAF2F8",
                        activebackground="#243746", activeforeground="#FFFFFF",
                        relief="solid", borderwidth=1,
                        highlightthickness=2,
                        highlightbackground="#FFFFFF", highlightcolor="#FFFFFF"
                    )
                else:
                    # WIFI_437: in modalita' GIORNO il pulsante ESPORTA GRAFICO
                    # deve tornare SEMPRE al giallo originale, anche dopo un
                    # precedente passaggio in modalita' notte.
                    _export_btn.configure(
                        bg="#B8860B", fg="#FFFFFF",
                        activebackground="#D4A017", activeforeground="#FFFFFF",
                        relief="solid", borderwidth=1,
                        highlightthickness=1,
                        highlightbackground="#8B6508", highlightcolor="#8B6508"
                    )
                _export_btn.lift()
            except Exception:
                pass

        # Il grande banner operativo (AVVISO / PASSIVA / ATTIVA) ha sempre
        # contorno BIANCO in modalita' notturna e NERO in modalita' diurna.
        try:
            self._apply_operation_banner_border()
        except Exception:
            pass

        # AVVIA/FERMA operativi seguono il tema; i pulsanti in lampeggio
        # vengono lasciati al loro colore temporaneo.
        for _name in (
            "aireplay_ng_router_start_button", "aireplay_ng_router_stop_button",
            "aireplay_ng_client_start_button", "aireplay_ng_client_stop_button",
            "start_capture_button", "stop_capture_button",
            "start_disturb_button", "stop_disturb_button"
        ):
            _btn=getattr(self,_name,None)
            if _btn is None:
                continue
            if _name in getattr(self, "_button_blink_after", {}):
                continue
            try:
                if night:
                    _btn.configure(bg="#111111",fg="#d6d8dc",
                                   activebackground="#222222",activeforeground="#ffffff")
                else:
                    _btn.configure(bg="#e7e7e7",fg="#000000",
                                   activebackground="#f4f4f4",activeforeground="#000000")
            except Exception:
                pass

    def apply_display_theme(self, night):
        """
        Applica il tema senza alterare le dimensioni responsive.

        v199:
        - il tema cambia SOLO colori/aspetto;
        - font, rowheight, padding e scaling restano sotto il controllo
          di _apply_responsive_layout();
        - dopo ogni cambio NOTTE/GIORNO il responsive viene riapplicato
          più volte quando Tk ha terminato di ridisegnare i widget.
        """
        self.night_mode = bool(night)
        style = self.style

        if self.night_mode:
            bg = "#000000"
            panel = "#050505"
            field = "#0a0a0a"
            fg = "#d6d8dc"
            accent = "#46576b"
            heading = "#101010"
            button = "#111111"
            active = "#222222"
            selected = "#30445b"

            self.theme_button_text.set("VERSIONE\nDIURNA")

            style.configure(".", background=bg, foreground=fg)
            style.configure("TFrame", background=bg)
            style.configure("TLabel", background=bg, foreground=fg)
            style.configure(
                "TLabelframe",
                background=bg,
                foreground=fg,
                bordercolor="#383d46"
            )
            style.configure(
                "TLabelframe.Label",
                background=bg,
                foreground=fg
            )
            style.configure(
                "TButton",
                background=button,
                foreground=fg,
                bordercolor="#3a404a",
                focusthickness=1,
                focuscolor="#4e5968"
            )
            style.map(
                "TButton",
                background=[("active", active), ("pressed", "#1d2026")],
                foreground=[("disabled", "#70757e")]
            )
            style.configure(
                "ThemeToggle.TButton",
                background="#303844",
                foreground="#f0f2f5",
                font=("TkDefaultFont", 11, "bold"),
                padding=(12, 10),
                anchor="center"
            )
            style.map(
                "ThemeToggle.TButton",
                # NOTTE: hover bianco opaco/sbiadito.
                background=[
                    ("pressed", "#BEBEBE"),
                    ("active", "#E0E0E0"),
                ],
                foreground=[
                    ("pressed", "#404040"),
                    ("active", "#505050"),
                ]
            )
            style.configure(
                "TEntry",
                fieldbackground=field,
                foreground=fg,
                insertcolor=fg,
                bordercolor="#454b55"
            )
            style.configure(
                "TCombobox",
                fieldbackground=field,
                background=field,
                foreground=fg,
                arrowcolor=fg
            )
            style.map(
                "TCombobox",
                fieldbackground=[("readonly", field)],
                foreground=[("readonly", fg)],
                selectbackground=[("readonly", field)],
                selectforeground=[("readonly", fg)]
            )
            # IMPORTANTE: niente rowheight/font qui.
            style.configure(
                "Treeview",
                background=panel,
                fieldbackground=panel,
                foreground=fg,
                bordercolor="#353a43"
            )
            style.configure(
                "Scanner.Treeview",
                background=panel,
                fieldbackground=panel,
                foreground=fg,
                bordercolor="#353a43"
            )
            style.configure(
                "Camera.Treeview",
                background=panel,
                fieldbackground=panel,
                foreground=fg,
                bordercolor="#353a43"
            )
            style.map(
                "Treeview",
                background=[("selected", selected)],
                foreground=[("selected", "#ffffff")]
            )
            style.map(
                "Scanner.Treeview",
                background=[("selected", selected)],
                foreground=[("selected", "#ffffff")]
            )
            style.map(
                "Camera.Treeview",
                background=[("selected", selected)],
                foreground=[("selected", "#ffffff")]
            )
            # IMPORTANTE: niente font qui.
            style.configure(
                "Treeview.Heading",
                background=heading,
                foreground=fg
            )
            style.map(
                "Treeview.Heading",
                background=[("active", "#303640")]
            )
            style.configure(
                "Horizontal.TProgressbar",
                background=accent,
                troughcolor="#262a31",
                bordercolor="#262a31"
            )
            style.configure(
                "Work.Horizontal.TProgressbar",
                background="#0B5FAE",
                troughcolor="#262a31",
                bordercolor="#262a31",
                lightcolor="#1687E8",
                darkcolor="#084A88"
            )
            style.configure(
                "TCheckbutton",
                background=bg,
                foreground=fg
            )

        else:
            bg = "#f0f0f0"
            fg = "#000000"

            self.theme_button_text.set("VERSIONE\nNOTTURNA")

            style.configure(".", background=bg, foreground=fg)
            style.configure("TFrame", background=bg)
            style.configure("TLabel", background=bg, foreground=fg)
            style.configure("TLabelframe", background=bg, foreground=fg)
            style.configure("TLabelframe.Label", background=bg, foreground=fg)
            style.configure(
                "TButton",
                background="#e7e7e7",
                foreground=fg,
                bordercolor="#b7b7b7"
            )
            style.map(
                "TButton",
                background=[("active", "#f4f4f4"), ("pressed", "#d5d5d5")]
            )
            style.configure(
                "ThemeToggle.TButton",
                background="#e7e7e7",
                foreground=fg,
                font=("TkDefaultFont", 11, "bold"),
                padding=(12, 10),
                anchor="center"
            )
            style.map(
                "ThemeToggle.TButton",
                # GIORNO: hover scuro con testo chiaro.
                background=[
                    ("pressed", "#20252B"),
                    ("active", "#343A40"),
                ],
                foreground=[
                    ("pressed", "#FFFFFF"),
                    ("active", "#F2F2F2"),
                ]
            )
            style.configure(
                "TEntry",
                fieldbackground="white",
                foreground=fg,
                insertcolor=fg,
                bordercolor="#b5b5b5"
            )
            style.configure(
                "TCombobox",
                fieldbackground="white",
                background="white",
                foreground=fg,
                arrowcolor=fg
            )
            style.map(
                "TCombobox",
                fieldbackground=[("readonly", "white")],
                foreground=[("readonly", fg)],
                selectbackground=[("readonly", "white")],
                selectforeground=[("readonly", fg)]
            )
            # IMPORTANTE: niente rowheight/font qui.
            style.configure(
                "Treeview",
                background="white",
                fieldbackground="white",
                foreground=fg
            )
            # Anche gli stili personalizzati devono avere esplicitamente
            # lo sfondo bianco: con il tema clam non ereditano sempre Treeview.
            style.configure(
                "Scanner.Treeview",
                background="white",
                fieldbackground="white",
                foreground=fg
            )
            style.configure(
                "Camera.Treeview",
                background="white",
                fieldbackground="white",
                foreground=fg
            )
            style.map(
                "Treeview",
                background=[("selected", "#3478bf")],
                foreground=[("selected", "white")]
            )
            style.map(
                "Scanner.Treeview",
                background=[("selected", "#3478bf")],
                foreground=[("selected", "white")]
            )
            style.map(
                "Camera.Treeview",
                background=[("selected", "#3478bf")],
                foreground=[("selected", "white")]
            )
            # IMPORTANTE: niente font qui.
            style.configure(
                "Treeview.Heading",
                background="#e5e5e5",
                foreground=fg
            )
            style.configure(
                "Horizontal.TProgressbar",
                background="#4a90d9",
                troughcolor="#e1e1e1"
            )
            style.configure(
                "Work.Horizontal.TProgressbar",
                background="#4a90d9",
                troughcolor="#e1e1e1",
                bordercolor="#b8b8b8",
                lightcolor="#4a90d9",
                darkcolor="#4a90d9"
            )
            style.configure("TCheckbutton", background=bg, foreground=fg)

        try:
            self.root.configure(background=bg)
            self.root.attributes("-alpha", 1.0)
        except Exception:
            pass

        self._configure_plain_tk_widgets(self.night_mode)
        try:
            self._apply_debug_panel_theme()
        except Exception:
            pass

        # Ripristina i colori indipendenti dopo il cambio tema.
        self._set_work_progress_color(
            getattr(self, "work_progress_color", "blue"))
        self._enforce_scan_progress_blue()

        # Riapplica subito il responsive sulle dimensioni correnti.
        self._reapply_responsive_after_theme()
        try:
            self._enforce_tree_heading_theme()
        except Exception:
            pass

        # L'overlay SCORE è composto da tk.Label separati dalla Treeview:
        # va quindi ridisegnato esplicitamente dopo ogni cambio GIORNO/NOTTE.
        try:
            self._refresh_lan_score_font_overlay()
            self.root.after(40, self._refresh_lan_score_font_overlay)
            self.root.after(150, self._refresh_lan_score_font_overlay)
        except Exception:
            pass



    def _enforce_tree_heading_theme(self):
        """
        Mantiene leggibili tutte le intestazioni delle tabelle anche al passaggio
        del mouse, in modalità giorno e notte.
        """
        try:
            dark = bool(getattr(self, "night_mode", False))

            if dark:
                normal_bg = "#101010"
                hover_bg = "#2A2F36"
                pressed_bg = "#20242A"
                fg = "#E6E6E6"
            else:
                normal_bg = "#E5E5E5"
                hover_bg = "#D2D2D2"
                pressed_bg = "#C4C4C4"
                fg = "#000000"

            for style_name in (
                "Treeview.Heading",
                "Scanner.Treeview.Heading",
                "Camera.Treeview.Heading",
            ):
                try:
                    self.style.configure(
                        style_name,
                        background=normal_bg,
                        foreground=fg
                    )
                    self.style.map(
                        style_name,
                        background=[
                            ("pressed", pressed_bg),
                            ("active", hover_bg),
                        ],
                        foreground=[
                            ("pressed", fg),
                            ("active", fg),
                        ]
                    )
                except Exception:
                    pass
        except Exception:
            pass

    def _reapply_responsive_after_theme(self):
        """
        Riapplica il layout responsive dopo un cambio tema.

        Il cambio stile ttk può provocare più passaggi di geometry management:
        per questo vengono fatti tre ricalcoli brevemente distanziati.
        """
        old_ids = getattr(self, "_theme_responsive_after_ids", [])
        for aid in old_ids:
            try:
                self.root.after_cancel(aid)
            except Exception:
                pass

        self._theme_responsive_after_ids = []

        def recalc():
            try:
                self.root.update_idletasks()
            except Exception:
                pass
            try:
                w = max(1, int(self.root.winfo_width()))
                h = max(1, int(self.root.winfo_height()))
                self._last_responsive_size = (w, h)
                self._apply_responsive_layout(w, h)
            except Exception:
                pass

        # immediato + dopo il primo/secondo ridisegno ttk
        recalc()
        for delay in (80, 250, 650):
            try:
                aid = self.root.after(delay, recalc)
                self._theme_responsive_after_ids.append(aid)
            except Exception:
                pass

    def _stop_passive_mode_banner_blink(self):
        """Ferma il lampeggio del banner MODALITA' PASSIVA/PASSIVE MODE."""
        try:
            aid = getattr(self, "_passive_mode_banner_blink_after", None)
            if aid is not None:
                self.root.after_cancel(aid)
        except Exception:
            pass
        self._passive_mode_banner_blink_after = None
        self._passive_mode_banner_blink_phase = False
        self._passive_mode_banner_blink_run_id = None

    def _start_passive_mode_banner_blink(self, run_id):
        """Lampeggia in blu fino alla fine della cattura passiva corrente."""
        self._stop_passive_mode_banner_blink()
        self._passive_mode_banner_blink_run_id = run_id
        self._passive_mode_banner_blink_phase = False

        def tick():
            try:
                if int(getattr(self, "capture_run_id", -1)) != int(run_id):
                    self._stop_passive_mode_banner_blink()
                    return
                if getattr(self, "operation_mode", "idle") != "passive":
                    self._stop_passive_mode_banner_blink()
                    return

                self._passive_mode_banner_blink_phase = not bool(
                    getattr(self, "_passive_mode_banner_blink_phase", False)
                )
                dark = bool(getattr(self, "night_mode", False))

                if self._passive_mode_banner_blink_phase:
                    bg = "#00BFFF" if dark else "#1565C0"
                else:
                    bg = "#075A9C" if dark else "#4A90E2"

                self.monitor_chip_warning.configure(bg=bg, fg="#FFFFFF")
                self._passive_mode_banner_blink_after = self.root.after(500, tick)
            except Exception:
                self._passive_mode_banner_blink_after = None

        tick()

    def _apply_operation_banner_border(self):
        """Applica il contorno del grande banner operativo in base al tema."""
        try:
            banner = getattr(self, "monitor_chip_warning", None)
            if banner is None:
                return
            dark = bool(getattr(self, "night_mode", False))
            border = "#FFFFFF" if dark else "#000000"
            banner.configure(
                relief="solid",
                borderwidth=0,
                highlightthickness=2,
                highlightbackground=border,
                highlightcolor=border
            )
            banner.lift()
        except Exception:
            pass

    def _set_operation_mode_banner(self, mode):
        """Aggiorna il grande riquadro superiore in base alla modalità operativa."""
        try:
            # Durante aireplay-ng/DISTURBO la MODALITA' ATTIVA ha priorità assoluta:
            # nessuna callback secondaria può riportare il banner al verde prima
            # che siano conclusi TUTTI i cicli e la barra abbia raggiunto il 100%.
            if bool(getattr(self, "_disturb_active_ui_lock", False)):
                mode = "active"
            # Durante AVVIA CATTURA manuale, in assenza di DISTURBO, la modalità
            # PASSIVA resta visibile per tutta la cattura.
            elif bool(getattr(self, "_manual_capture_banner_active", False)):
                mode = "passive"
            if mode == "passive":
                self.operation_mode = "passive"
                label = "PASSIVE MODE" if getattr(self, "language", "it") == "en" else "MODALITA' PASSIVA"
                self.monitor_chip_warning.configure(
                    text=label,
                    bg=("#082A50" if getattr(self, "night_mode", False) else "#1565C0"),
                    fg=("white" if not getattr(self, "night_mode", False) else "#DCE8F3"),
                    font=("TkDefaultFont", 18, "bold"),
                    justify="center",
                    anchor="center"
                )
            elif mode == "active":
                self.operation_mode = "active"
                label = "ACTIVE MODE" if getattr(self, "language", "it") == "en" else "MODALITA' ATTIVA"
                self.monitor_chip_warning.configure(
                    text=label,
                    bg=("#741A1A" if getattr(self, "night_mode", False) else "#C62828"),
                    fg=("white" if not getattr(self, "night_mode", False) else "#F3DCDC"),
                    font=("TkDefaultFont", 18, "bold"),
                    justify="center",
                    anchor="center"
                )
            else:
                self.operation_mode = "idle"
                label = (
                    "THE SOFTWARE WORKS EXCLUSIVELY WITH WIFI CHIPSETS THAT CAN BE CONFIGURED IN MONITOR MODE"
                    if getattr(self, "language", "it") == "en"
                    else "IL SOFTWARE FUNZIONA ESCLUSIVAMENTE CON CIP WIFI CHE POSSONO ESSERE CONFIGURATI IN MODALITA' MONITORAGGIO"
                )
                self.monitor_chip_warning.configure(
                    text=label,
                    bg=("#173D19" if getattr(self, "night_mode", False) else "#2E7D32"),
                    fg=("white" if not getattr(self, "night_mode", False) else "#DCE8DF"),
                    font=("TkDefaultFont", 9, "bold"),
                    justify="center",
                    anchor="center"
                )
            # Il bordo deve essere identico in AVVISO, PASSIVA e ATTIVA.
            self._apply_operation_banner_border()
        except Exception:
            pass

    def _translate_dialog_text(self, value):
        """Traduce titoli e messaggi dei dialoghi quando la lingua è ENG."""
        text = str(value)
        if getattr(self, "language", "it") != "en":
            return text

        # Frasi complete più frequenti.
        exact = {
            "Dipendenze mancanti": "Missing dependencies",
            "Permessi": "Permissions",
            "Mancano: ": "Missing: ",
            "Avvia il programma tramite il launcher con sudo.": "Start the program using the launcher with sudo.",
            "Seleziona prima una interfaccia Wi-Fi valida.": "Select a valid Wi-Fi interface first.",
            "Monitor mode non supportata": "Monitor mode not supported",
            "Nessuna interfaccia risulta in monitor mode.": "No interface is currently in monitor mode.",
            "Router": "Router",
            "Seleziona prima un router.": "Select a router first.",
            "Canale": "Channel",
            "Canale non valido.": "Invalid channel.",
            "BLOCCO": "BLOCK",
            "BLOCCO CLIENT": "BLOCK CLIENT",
            "Seleziona prima un router/BSSID valido.": "Select a valid router/BSSID first.",
            "Seleziona prima una interfaccia WLAN valida.": "Select a valid WLAN interface first.",
            "Seleziona prima un CLIENT/MAC valido.": "Select a valid CLIENT/MAC first.",
            "Comando airodump-ng non trovato nel PATH.": "airodump-ng command not found in PATH.",
            "Seleziona prima un BSSID/router valido.": "Select a valid BSSID/router first.",
            "Il canale selezionato non e valido.": "The selected channel is invalid.",
            "Seleziona prima un MAC client valido.": "Select a valid client MAC first.",
            "Durata, ripetizioni e attesa devono essere numeri interi.": "Duration, repetitions and pause must be integer values.",
            "Il comando aireplay-ng non e stato trovato nel PATH.": "The aireplay-ng command was not found in PATH.",
            "BSSID": "BSSID",
            "Seleziona un router dall'elenco.": "Select a router from the list.",
            "Client": "Client",
            "MAC client non valido.": "Invalid client MAC.",
            "Esporta": "Export",
            "La cartella CATTURE è vuota.": "The CATTURE folder is empty.",
            "Seleziona prima un file.": "Select a file first.",
            "Il file selezionato non è più disponibile.": "The selected file is no longer available.",
            "PCAP": "PCAP",
            "Nessun file PCAP disponibile da aprire.": "No PCAP file is available to open.",
            "Wireshark": "Wireshark",
            "Wireshark non risulta installato o non è nel PATH.": "Wireshark is not installed or is not in PATH.",
            "Non sono disponibili né pkexec né sudo per avviare Wireshark come amministratore.":
                "Neither pkexec nor sudo is available to start Wireshark with administrator privileges.",
        }
        if text in exact:
            return exact[text]

        # Sostituzioni per messaggi dinamici/f-string.
        replacements = [
            ("Scansione router", "Router scan"),
            ("Scansione client", "Client scan"),
            ("Scansione completata", "Scan completed"),
            ("Scansione arrestata", "Scan stopped"),
            ("Scansione in corso", "Scan in progress"),
            ("Cattura passiva", "Passive capture"),
            ("Cattura terminata", "Capture completed"),
            ("Cattura arrestata", "Capture stopped"),
            ("Disturbo", "Disruption"),
            ("Arresto DISTURBO", "Stopping DISRUPTION"),
            ("Handshake trovato", "Handshake found"),
            ("Ricerca Client Associati a:", "Scan clients associated with:"),
            ("Router selezionato:", "Selected router:"),
            ("Client rilevati per", "Clients detected for"),
            ("Numero:", "Count:"),
            ("non risulta una scheda Wi-Fi USB esterna.", "is not detected as an external USB Wi-Fi adapter."),
            ("Seleziona la scheda USB. La Wi-Fi interna del PC non verrà modificata.",
             "Select the USB adapter. The PC's internal Wi-Fi interface will not be modified."),
            ("Errore sul comando:", "Error executing command:"),
            ("La sola scheda USB è stata ripristinata in managed.",
             "Only the USB adapter was restored to managed mode."),
            ("non risulta in type monitor dopo il tentativo.",
             "is not in monitor type after the attempt."),
            ("Seleziona prima un router/BSSID valido.", "Select a valid router/BSSID first."),
            ("Seleziona prima una interfaccia WLAN valida.", "Select a valid WLAN interface first."),
            ("Seleziona prima un CLIENT/MAC valido.", "Select a valid CLIENT/MAC first."),
            ("Errore avvio comando:", "Error starting command:"),
            ("Impossibile accedere alla cartella CATTURE:", "Unable to access the CATTURE folder:"),
            ("File esportato correttamente:", "File exported successfully:"),
            ("Errore durante l'esportazione:", "Error while exporting:"),
            ("Impossibile aprire il PCAP con privilegi amministrativi:",
             "Unable to open the PCAP with administrator privileges:"),
        ]
        for old, new in replacements:
            text = text.replace(old, new)

        return text

    def _install_translated_messageboxes(self):
        """Fa sì che showerror/showwarning/showinfo seguano la lingua della GUI."""
        if getattr(self, "_translated_messageboxes_installed", False):
            return
        self._translated_messageboxes_installed = True

        def wrap(original):
            def translated(title, message, *args, **kwargs):
                return original(
                    self._translate_dialog_text(title),
                    self._translate_dialog_text(message),
                    *args,
                    **kwargs
                )
            return translated

        messagebox.showerror = wrap(self._messagebox_showerror_original)
        messagebox.showwarning = wrap(self._messagebox_showwarning_original)
        messagebox.showinfo = wrap(self._messagebox_showinfo_original)

    def _translate_static_widgets(self, language):
        """Traduce i testi statici principali della GUI."""
        it_en = {
            "AGGIORNA INTERFACCIE WIFI": "REFRESH WI-FI INTERFACES",
            "ATTIVA MONITOR MODE": "ENABLE MONITOR MODE",
            "SCANSIONA RETI WIFI": "SCAN WI-FI NETWORKS",
            "SCANSIONA CLIENT DELL'AP SELEZIONATO": "SCAN CLIENTS OF SELECTED AP",
            "STOP RICERCA": "STOP SEARCH",
            "Rilevamento Routers WIFI": "WiFi Router Detection",
            "ROUTER RILEVATI": "DETECTED ROUTERS",
            "DISPOSITIVI CLIENT WIFI": "ASSOCIATED WI-FI CLIENTS",
            "POSSIBILI DISPOSITIVI LAN": "LAN-SIDE DEVICES",
            "SCANSIONE LAN ATTIVA": "ACTIVE LAN SCAN",
            "BLOCCO/CATTURA": "BLOCK/CAPTURE",
            "BLOCCO": "BLOCK",
            "CANALE:": "CHANNEL:",
            "DURATA (sec):": "DURATION (sec):",
            "RIPETIZIONI:": "REPETITIONS:",
            "PAUSA (sec):": "PAUSE (sec):",
            "ESPORTA CATTURA": "EXPORT CAPTURE",
            "ESPORTA HANDSHAKE": "EXPORT HANDSHAKE",
            "TERMINA SE TROVI HANDSHAKE": "STOP WHEN HANDSHAKE IS FOUND",
            "MACS CATTURATI": "OBSERVED MAC ADDRESSES",
            "POSSIBILI TELECAMERE RILEVATE": "POSSIBLE CAMERA DEVICES",
            "AVVIA": "START",
            "FERMA": "STOP",
            "ESCI": "EXIT",
            "PULISCI": "CLEAR",
            "INTERFACCIA WIFI": "WI-FI INTERFACE",
            "ORIGINE:": "ORIGIN:",
            "MONITOR MODE:": "MONITOR MODE:",
            "NUMERO:": "NUMBER:",
            "ROUTER": "ROUTER",
            "CLIENT": "CLIENT",
            "CATTURA PASSIVA": "PASSIVE CAPTURE",
            "DISTURBO": "DISRUPTION",
            "CRIPTAZIONE": "SECURITY",
            "POTENZA": "SIGNAL",
            "PACCHETTI": "FRAMES",
            "STAZIONI": "STATIONS",
            "DISPOSITIVO": "DEVICE",
            "VENDITORE": "VENDOR",
            "EVIDENZE": "EVIDENCE",
            "SONDA": "PROBES",
            "DEBUG SEQUENZA COMANDI / ESITO": "DEBUG COMMAND SEQUENCE / RESULT",
            "DATA / ORA": "DATE / TIME",
            "DIMENSIONE": "SIZE",
            "ESPORTA FILE SELEZIONATO": "EXPORT SELECTED FILE",
            "CHIUDI": "CLOSE",
        }
        en_it = {v: k for k, v in it_en.items()}
        mapping = it_en if language == "en" else en_it

        def walk(widget):
            try:
                current = widget.cget("text")
                if current in mapping:
                    widget.configure(text=mapping[current])
            except Exception:
                pass
            try:
                for child in widget.winfo_children():
                    walk(child)
            except Exception:
                pass
        walk(self.root)

        tree_en = {
            "ap_tree":{
                "bssid":"BSSID","ch":"CHANNEL","band":"BAND","clients":"CLIENTS",
                "packets":"FRAMES","enc":"SECURITY","pwr":"SIGNAL","essid":"ESSID"
            },
            "client_tree":{
                "station":"STATIONS","resolved":"DEVICE","vendor":"VENDOR",
                "pwr":"SIGNAL","packets":"FRAMES","probes":"PROBES","source":"SOURCE"
            },
            "lan_vendor_tree":{
                "vendor":"VENDOR","role":"ROLE","macs":"MAC ADDRESSES","score":"SC","level":"LIKELIHOOD","source":"SOURCE"
            },
            "res_tree":{
                "mac":"MAC","vendor":"VENDOR","class":"CLASS",
                "evidence":"EVIDENCE","notes":"NOTES","source":"SOURCE"
            },
            "camera_tree":{
                "mac":"MAC","vendor":"VENDOR","score":"SCORE","level":"LIKELIHOOD",
                "txrx":"TX/RX","provenance":"SOURCE","duration":"DURATION","indicators":"INDICATORS"
            }
        }
        tree_it = {
            "ap_tree":{"bssid":"BSSID","ch":"CANALE","band":"BANDA","clients":"CLIENTI","packets":"PACCHETTI","enc":"CRIPTAZIONE","pwr":"POTENZA","essid":"ESSID"},
            "client_tree":{"station":"STAZIONI","resolved":"DISPOSITIVO","vendor":"VENDITORE","pwr":"POTENZA","packets":"PACCHETTI","probes":"SONDA","source":"PROVENIENZA"},
            "lan_vendor_tree":{"vendor":"VENDITORE","role":"RUOLO","macs":"MACS","score":"SC","level":"PROBABILITA'","source":"PROVENIENZA"},
            "res_tree":{"mac":"MAC","vendor":"VENDITORE","class":"CLASSE","evidence":"PROVA","notes":"NOTE","source":"PROVENIENZA"},
            "camera_tree":{"mac":"MAC","vendor":"VENDITORE","score":"SCORE","level":"PROBABILITA'","txrx":"TX/RX","provenance":"PROVENIENZA","duration":"DURATA (sec)"}
        }
        tree_map = tree_en if language == "en" else tree_it
        for tree_name, headings in tree_map.items():
            tree = getattr(self, tree_name, None)
            if tree is None:
                continue
            for col, title in headings.items():
                try:
                    tree.heading(col, text=title)
                except Exception:
                    pass


    def _lang(self, it_text, en_text):
        """Return text in the currently selected GUI language."""
        return en_text if getattr(self, "language", "it") == "en" else it_text

    def _mac_class_for_language(self, value):
        s=str(value or "")
        if getattr(self,"language","it") != "en":
            return s
        return {
            "Wi-Fi ASSOCIATO":"ASSOCIATED WI-FI CLIENT",
            "LAN CANDIDATO":"LAN-SIDE CANDIDATE",
            "ALTRO/INCERTO":"OTHER / UNCERTAIN",
            "MULTICAST/BROADCAST":"MULTICAST / BROADCAST",
            "AP":"ACCESS POINT",
        }.get(s,s)

    def _analysis_text_for_language(self, value):
        """Translate internally generated analysis prose for English presentation."""
        s=str(value or "")
        if getattr(self,"language","it") != "en":
            return s

        replacements=[
            ("MOLTO PROBABILE","HIGHLY LIKELY"),
            ("PROBABILE","LIKELY"),
            ("POSSIBILE","POSSIBLE"),
            ("DA OSSERVARE","LOW CONFIDENCE"),
            ("ALTA confidenza","HIGH confidence"),
            ("ALTA","HIGH"),
            ("MEDIA","MODERATE"),
            ("BASSA","LOW"),
            ("EVIDENZA SINGOLA","SINGLE INDICATOR"),
            ("BSSID selezionato","Selected BSSID"),
            ("Router/access point oggetto della cattura","Router/access point being captured"),
            ("Indirizzo gruppo/servizio","Group/service address"),
            ("Non contato come dispositivo","Not counted as a device"),
            ("frame radio infrastruttura","infrastructure radio frame"),
            ("management radio","radio management traffic"),
            ("Wi-Fi PROBABILE: client visto via radio; associazione attiva non provata dai frame DATA",
             "POSSIBLE WI-FI CLIENT: station observed over the air; active association not confirmed by DATA frames"),
            ("MAC osservato direttamente come station Wi-Fi dell'AP",
             "MAC address observed directly as a Wi-Fi station of the access point"),
            ("presenza nel PCAP senza ruolo univoco",
             "present in the PCAP without an unambiguous role"),
            ("Ruolo non determinabile con sicurezza",
             "Role cannot be determined with confidence"),
            ("client selezionato","selected client"),
            ("Servizio","Service"),
            ("Sconosciuto","Unknown"),
            ("MAC osservato come endpoint del Distribution System",
             "MAC address observed as a Distribution System (DS)-side endpoint"),
            ("evidenze=","DS indicators="),
            ("durata=","observed duration="),
            ("byte osservati=","observed bytes="),
            ("Escluso automaticamente se compare anche come station Wi-Fi.",
             "Automatically excluded if it also appears as a Wi-Fi station."),
            ("Classificazione basata sugli header 802.11 del BSSID nel PCAP, leggibili anche senza password WPA/WPA2.",
             "Classification is based on IEEE 802.11 header fields for the selected BSSID, which remain observable without the WPA/WPA2 passphrase."),
            ("Indica un endpoint lato Distribution System, ma non può dimostrare da sola il collegamento fisico Ethernet.",
             "It indicates a Distribution System (DS)-side endpoint, but does not by itself prove a physical Ethernet connection."),
            ("flusso continuo","continuous traffic flow"),
            ("traffico sostenuto","sustained traffic"),
            ("sessione persistente","persistent session"),
            ("molti frame grandi","high proportion of large frames"),
            ("temporizzazione regolare","regular timing pattern"),
            ("segnale stabile","stable RF signal"),
            ("download dominante","download-dominant traffic"),
            ("traffico a burst","bursty traffic"),
            ("solo piccoli pacchetti","small-frame-only pattern"),
            ("profilo consumer/download","consumer/download-oriented profile"),
            ("presenza Wi-Fi stabile","stable Wi-Fi presence"),
            ("vendor camera","camera-oriented vendor/OUI"),
            ("vendor IoT","IoT-oriented vendor/OUI"),
            ("upload video prevalente","video-like uplink dominance"),
            ("upload prevalente","uplink-dominant traffic"),
            ("vendor client generico","generic client-device vendor"),
            ("vendor media/TV","media/TV-device vendor"),
            ("metadati 802.11 compatibili","compatible IEEE 802.11 traffic metadata"),
            ("NON DETERMINATA","UNDETERMINED"),
            ("NON DETERMINABILE DAL SOLO TRAFFICO","NOT DETERMINABLE FROM TRAFFIC ALONE"),
        ]
        for a,b in replacements:
            s=s.replace(a,b)
        return s

    def _mac_row_for_language(self, row):
        if len(row) < 5:
            return row
        mac,vendor,cls,evidence,notes=row[:5]
        vendor = "Unknown" if (getattr(self,"language","it")=="en" and str(vendor)=="Sconosciuto") else vendor
        return (
            mac,
            vendor,
            self._mac_class_for_language(cls),
            self._analysis_text_for_language(evidence),
            self._analysis_text_for_language(notes),
        )

    def _camera_reason_for_language(self, value):
        return self._analysis_text_for_language(value)

    def _refresh_language_dynamic_texts(self):
        bssid = (self.bssid.get() or "").strip() or "--"
        client = (self.client.get() or "").strip() or "--"

        if self.language == "en":

            self.theme_button_text.set("DAY VERSION" if self.night_mode else "NIGHT VERSION")
            self.passive_box_title.set(f"PASSIVE CAPTURE   BSSID: {bssid}")
            self.disturb_box_title.set(f"DISRUPTION   BSSID: {bssid} / CLIENT: {client}")

            cap = self.client_search_caption.get()
            tail = cap.split(":", 1)[-1].strip() if ":" in cap else "--"
            self.client_search_caption.set(f"Scan clients associated with: {tail}")

            try:
                self.router_count.set(f"Count: {self.router_count.get().split(':')[-1].strip()}")
                self.client_count.set(f"Count: {self.client_count.get().split(':')[-1].strip()}")
                self.probable_lan_vendor_count.set(
                    f"Count: {self.probable_lan_vendor_count.get().split(':')[-1].strip()}"
                )
            except Exception:
                pass

            iface = (self.iface.get() or "").strip()
            if iface:
                origin = "USB / EXTERNAL" if self.is_usb_network_interface(iface) else "PC / INTERNAL"
                self.iface_origin.set(f": {origin}")
            else:
                self.iface_origin.set(": --")
        else:

            self.theme_button_text.set("VERSIONE\nDIURNA" if self.night_mode else "VERSIONE\nNOTTURNA")
            self.passive_box_title.set(f"CATTURA PASSIVA   BSSID: {bssid}")
            self.disturb_box_title.set(f"DISTURBO   BSSID: {bssid} / CLIENT: {client}")

            cap = self.client_search_caption.get()
            tail = cap.split(":", 1)[-1].strip() if ":" in cap else "--"
            self.client_search_caption.set(f"Ricerca Client Associati a: {tail}")

            try:
                self.router_count.set(f"Numero: {self.router_count.get().split(':')[-1].strip()}")
                self.client_count.set(f"Numero: {self.client_count.get().split(':')[-1].strip()}")
                self.probable_lan_vendor_count.set(
                    f"Numero: {self.probable_lan_vendor_count.get().split(':')[-1].strip()}"
                )
            except Exception:
                pass
            self.iface_origin.set(self.interface_origin_text(self.iface.get()))
        self._set_operation_mode_banner(getattr(self, "operation_mode", "idle"))

    def apply_language(self, language):
        self.language = "en" if language == "en" else "it"
        self._translate_static_widgets(self.language)
        self._refresh_language_dynamic_texts()
        try:
            self.export_capture_button_text.set(
                "EXPORT" if self.language == "en" else "ESPORTA"
            )
        except Exception:
            pass

        # Aggiorna i livelli di probabilità LAN già presenti.
        try:
            for item in self.lan_vendor_tree.get_children():
                vals=list(self.lan_vendor_tree.item(item,"values"))
                if len(vals)>=4:
                    score=self._lan_score_from_evidence(vals[2])
                    vals[3]=self._lan_level_from_score(score)
                    self.lan_vendor_tree.item(item,values=vals)
        except Exception:
            pass

        # Aggiorna immediatamente gli stati HANDSHAKE nella lingua selezionata.
        try:
            if getattr(self, "handshake_latched", False):
                self.handshake_state.set(self._handshake_word(True))
                self.handshake_m1.set(self._handshake_part_word(True))
                self.handshake_m2.set(self._handshake_part_word(True))
                self.handshake_m3.set(self._handshake_part_word(True))
                self.handshake_m4.set(self._handshake_part_word(True))
            else:
                self.handshake_state.set(self._handshake_word(False))
                found = set(str(x) for x in getattr(self, "handshake_latched_msgs", set()))
                self.handshake_m1.set(self._handshake_part_word("1" in found))
                self.handshake_m2.set(self._handshake_part_word("2" in found))
                self.handshake_m3.set(self._handshake_part_word("3" in found))
                self.handshake_m4.set(self._handshake_part_word("4" in found))
        except Exception:
            pass
        # Refresh visible MAC analysis rows in the selected language without
        # altering the raw analysis data used internally.
        try:
            visible={}
            for item in self.res_tree.get_children():
                vals=self.res_tree.item(item,"values")
                if vals:
                    visible[str(vals[0]).lower()]=item
            for mac,raw in getattr(self,"live_mac_rows",{}).items():
                if mac in visible:
                    self.res_tree.item(visible[mac],values=self._mac_row_for_language(raw))
        except Exception:
            pass

        # Refresh camera likelihood labels and cached rationale strings.
        try:
            for item in self.camera_tree.get_children():
                vals=list(self.camera_tree.item(item,"values"))
                if len(vals)>=4:
                    mm=re.search(r"(\d{1,3})",str(vals[2]))
                    score=int(mm.group(1)) if mm else 0
                    if self.language=="en":
                        vals[3]="HIGHLY LIKELY" if score>=80 else "LIKELY" if score>=62 else "POSSIBLE" if score>=42 else "LOW CONFIDENCE"
                    else:
                        vals[3]="MOLTO PROBABILE" if score>=80 else "PROBABILE" if score>=62 else "POSSIBILE" if score>=42 else "DA OSSERVARE"
                    self.camera_tree.item(item,values=vals)
        except Exception:
            pass



    def toggle_language(self):
        """Language switching is disabled in this fixed English edition."""
        self.language = "en"
        try:
            self.apply_language("en")
        except Exception:
            pass

    def _apply_camera_detail_theme(self, win, text_widget=None):
        """Compatibilità: usa il nuovo tema dettagli telecamera."""
        self._force_camera_detail_dark_theme(win)



    def _show_camera_detail_without_flash(self, win):
        """Mostra il popup dettagli solo dopo che il tema è stato applicato."""
        try:
            win.withdraw()
        except Exception:
            pass

        try:
            self._force_camera_detail_dark_theme(win)
        except Exception:
            pass

        def reveal():
            try:
                self._force_camera_detail_dark_theme(win)
            except Exception:
                pass
            try:
                win.update_idletasks()
            except Exception:
                pass
            try:
                win.deiconify()
                win.lift()
            except Exception:
                pass

        try:
            # Un solo ciclo idle è sufficiente per costruire i widget senza mostrarli bianchi.
            win.after_idle(reveal)
        except Exception:
            reveal()

    def _force_camera_detail_dark_theme(self, win):
        """Forza realmente il tema scuro su TUTTI i widget del popup dettagli telecamera."""
        try:
            dark = bool(getattr(self, "night_mode", False))
            if dark:
                bg = "#12171B"
                panel = "#1A2126"
                panel2 = "#20292F"
                fg = "#E7ECEF"
                muted = "#A9B4BA"
                border = "#334149"
                select_bg = "#2B4558"
                select_fg = "#FFFFFF"
            else:
                bg = "#ECEFF1"
                panel = "#FFFFFF"
                panel2 = "#F5F5F5"
                fg = "#111111"
                muted = "#555555"
                border = "#B0BEC5"
                select_bg = "#C9DDF4"
                select_fg = "#111111"

            try:
                win.configure(bg=bg)
            except Exception:
                pass

            # Stili ttk dedicati SOLO al popup telecamera.
            try:
                s = ttk.Style(win)
                s.configure("CameraDetail.TFrame", background=bg)
                s.configure("CameraDetailPanel.TFrame", background=panel)
                s.configure("CameraDetail.TLabel", background=bg, foreground=fg)
                s.configure("CameraDetailPanel.TLabel", background=panel, foreground=fg)
                s.configure("CameraDetailMuted.TLabel", background=panel, foreground=muted)
                s.configure("CameraDetail.TLabelframe", background=bg, bordercolor=border)
                s.configure("CameraDetail.TLabelframe.Label", background=bg, foreground=fg)
                s.configure(
                    "CameraDetail.Treeview",
                    background=panel,
                    fieldbackground=panel,
                    foreground=fg,
                    bordercolor=border,
                    rowheight=24
                )
                s.configure(
                    "CameraDetail.Treeview.Heading",
                    background=panel2,
                    foreground=fg,
                    bordercolor=border
                )
                s.map(
                    "CameraDetail.Treeview",
                    background=[("selected", select_bg)],
                    foreground=[("selected", select_fg)]
                )
                s.map(
                    "CameraDetail.Treeview.Heading",
                    background=[
                        ("pressed", panel2),
                        ("active", panel2)
                    ],
                    foreground=[
                        ("pressed", fg),
                        ("active", fg)
                    ]
                )
            except Exception:
                pass

            def walk(widget):
                try:
                    if isinstance(widget, tk.Text):
                        widget.configure(
                            bg=panel, fg=fg,
                            insertbackground=fg,
                            selectbackground=select_bg,
                            selectforeground=select_fg,
                            highlightbackground=border,
                            highlightcolor=border,
                            highlightthickness=1,
                            relief="flat"
                        )
                    elif isinstance(widget, tk.Listbox):
                        widget.configure(
                            bg=panel, fg=fg,
                            selectbackground=select_bg,
                            selectforeground=select_fg,
                            highlightbackground=border
                        )
                    elif isinstance(widget, tk.Canvas):
                        widget.configure(bg=bg, highlightbackground=border)
                    elif isinstance(widget, tk.LabelFrame):
                        widget.configure(bg=bg, fg=fg, highlightbackground=border)
                    elif isinstance(widget, tk.Frame):
                        widget.configure(bg=bg)
                    elif isinstance(widget, tk.Label):
                        widget.configure(bg=bg, fg=fg)
                    elif isinstance(widget, tk.Entry):
                        widget.configure(
                            bg=panel, fg=fg,
                            insertbackground=fg,
                            readonlybackground=panel
                        )
                except Exception:
                    pass

                # Applica gli style ttk anche ai figli ttk.
                try:
                    wc = widget.winfo_class()
                    if wc == "TFrame":
                        widget.configure(style="CameraDetail.TFrame")
                    elif wc == "TLabel":
                        widget.configure(style="CameraDetail.TLabel")
                    elif wc == "TLabelframe":
                        widget.configure(style="CameraDetail.TLabelframe")
                    elif wc == "Treeview":
                        widget.configure(style="CameraDetail.Treeview")
                except Exception:
                    pass

                try:
                    for child in widget.winfo_children():
                        walk(child)
                except Exception:
                    pass

            walk(win)

        except Exception:
            pass


    def _apply_scanner_button_colors(self):
        """Applica i colori definitivi dei due pulsanti scanner."""
        try:
            if getattr(self, "night_mode", False):
                bg = "#1E90FF"
                active = "#061E39"
                fg = "#DCE8F3"
            else:
                bg = "#006BFF"
                active = "#0052CC"
                fg = "white"

            for btn in (
                getattr(self, "scan_wifi_button", None),
                getattr(self, "scan_client_button", None),
            ):
                if btn is not None:
                    btn.configure(
                        bg=bg,
                        fg=fg,
                        activebackground=active,
                        activeforeground=fg,
                        disabledforeground=fg
                    )
                    try:
                        btn.configure(
                            highlightbackground=bg,
                            highlightcolor=active
                        )
                    except Exception:
                        pass
        except Exception:
            pass

    def toggle_night_mode(self):
        """Alterna tema mantenendo responsive e lingua selezionata."""
        # Congela x/y/width del riquadro verde durante il cambio tema:
        # nessun movimento laterale al primo passaggio GIORNO -> NOTTE.
        try:
            if hasattr(self, "_position_monitor_warning"):
                self._position_monitor_warning()
            self._warning_theme_transition_lock = True
        except Exception:
            pass

        self.apply_display_theme(not self.night_mode)
        self._refresh_language_dynamic_texts()

        # Aggiorna SUBITO testo, colore e soprattutto font del banner prima
        # che Tk esegua i ridisegni/after del cambio tema. In questo modo
        # non esiste più un frame intermedio con una dimensione diversa.
        try:
            self._set_operation_mode_banner(getattr(self, "operation_mode", "idle"))
        except Exception:
            pass

        try:
            if hasattr(self, "_position_monitor_warning"):
                self.root.after(120, self._position_monitor_warning)
        except Exception:
            pass

        # Aggiorna anche eventuali finestre dettagli telecamera già aperte.
        try:
            for child in self.root.winfo_children():
                try:
                    if isinstance(child, tk.Toplevel):
                        title = str(child.title()).lower()
                        if "camera" in title or "telecamera" in title:
                            self._force_camera_detail_dark_theme(child)
                except Exception:
                    pass
        except Exception:
            pass
        # FORZATURA FINALE COLORI PULSANTI SCANNER.
        # Deve essere l'ULTIMA modifica cromatica della funzione tema.
        try:
            if getattr(self, "night_mode", False):
                _scan_bg = "#1E90FF"
                _scan_active = "#061E39"
                _scan_fg = "#DCE8F3"
            else:
                _scan_bg = "#006BFF"
                _scan_active = "#0052CC"
                _scan_fg = "white"

            for _btn in (
                getattr(self, "scan_wifi_button", None),
                getattr(self, "scan_client_button", None),
            ):
                if _btn is not None:
                    _btn.configure(
                        bg=_scan_bg,
                        fg=_scan_fg,
                        activebackground=_scan_active,
                        activeforeground=_scan_fg,
                        disabledforeground=_scan_fg
                    )
                    # tk.Button può mantenere colori di highlight/relief precedenti:
                    # li riallineiamo esplicitamente.
                    try:
                        _btn.configure(
                            highlightbackground=_scan_bg,
                            highlightcolor=_scan_active
                        )
                    except Exception:
                        pass

            # WIFI_437: forzatura finale anche per ESPORTA GRAFICO.
            # Evita che il walk() del tema o un redraw successivo lasci il
            # pulsante con il colore scuro quando si torna alla modalita' giorno.
            try:
                _exp = getattr(self, "network_diagram_export_button", None)
                if _exp is not None:
                    if getattr(self, "night_mode", False):
                        _exp.configure(
                            bg="#101820", fg="#EAF2F8",
                            activebackground="#243746", activeforeground="#FFFFFF",
                            highlightthickness=2,
                            highlightbackground="#FFFFFF", highlightcolor="#FFFFFF"
                        )
                    else:
                        _exp.configure(
                            bg="#B8860B", fg="#FFFFFF",
                            activebackground="#D4A017", activeforeground="#FFFFFF",
                            highlightthickness=1,
                            highlightbackground="#8B6508", highlightcolor="#8B6508"
                        )
                    _exp.lift()
            except Exception:
                pass

            # Forza Tk a ridisegnare subito i due pulsanti col colore corretto.
            try:
                self.root.update_idletasks()
            except Exception:
                pass
        except Exception:
            pass
        # Esegui un ultimo riallineamento nel ciclo eventi successivo:
        # eventuali restore after(0) dei lampeggi sono già terminati.
        try:
            self.root.after(1, self._apply_scanner_button_colors)
        except Exception:
            pass
        try:
            self._refresh_cyborg_label()
        except Exception:
            pass
        try:
            self._apply_debug_panel_theme()
            self.root.after(5, self._apply_debug_panel_theme)
            self.root.after(80, self._apply_debug_panel_theme)
        except Exception:
            pass
        try:
            self._schedule_camera_block_buttons_refresh(80)
        except Exception:
            pass
        try:
            self._refresh_camera_block_button_theme()
        except Exception:
            pass
        try:
            self._refresh_iface_status_theme()
        except Exception:
            pass


        try:
            self.root.after(80, lambda: self._set_operation_mode_banner(
                getattr(self, "operation_mode", "idle")
            ))
            self.root.after(120, self._position_monitor_warning)
            self.root.after(260, self._position_monitor_warning)
        except Exception:
            pass

        try:
            def _unlock_warning_theme_geometry():
                self._warning_theme_transition_lock = False
            self.root.after(340, _unlock_warning_theme_geometry)
        except Exception:
            self._warning_theme_transition_lock = False

    def _apply_debug_panel_theme(self):
        """Aggiorna completamente il pannello DEBUG già aperto al tema corrente."""
        popup=getattr(self,"command_debug_window",None)
        try:
            if popup is None or not popup.winfo_exists():
                return
        except Exception:
            return

        dark=bool(getattr(self,"night_mode",False))
        bg="#12171B" if dark else "#ECEFF1"
        panel="#1A2126" if dark else "#FFFFFF"
        # Barra superiore DEBUG: grigia e ben distinguibile in modalità giorno;
        # in modalità notte resta volutamente discreta e poco invasiva.
        title_bg="#20272B" if dark else "#B0BEC5"
        fg="#D7DEE2" if dark else "#111111"
        border="#232C31" if dark else "#78909C"
        button_bg="#2B3940" if dark else "#455A64"
        button_active="#3C4F59" if dark else "#607D8B"
        select_bg="#2B4558" if dark else "#C9DDF4"
        select_fg="#FFFFFF" if dark else "#111111"

        try:
            popup.configure(
                bg=bg,
                highlightbackground=border,
                highlightcolor=border,
                highlightthickness=(1 if dark else 2),
                bd=0,
                relief="flat"
            )
        except Exception:
            pass

        # Primo frame = barra titolo del popup interno.
        try:
            titlebar=popup.winfo_children()[0]
        except Exception:
            titlebar=None

        def paint(widget):
            try:
                cls=widget.winfo_class()

                if isinstance(widget, tk.Text):
                    widget.configure(
                        bg=panel,
                        fg=fg,
                        insertbackground=fg,
                        selectbackground=select_bg,
                        selectforeground=select_fg,
                        highlightbackground=border,
                        highlightcolor=border,
                        borderwidth=0
                    )

                elif isinstance(widget, tk.Button):
                    # X, PULISCI/CLEAR, CHIUDI/CLOSE.
                    if titlebar is not None and widget.master is titlebar:
                        widget.configure(
                            bg=title_bg, fg=fg,
                            activebackground=border,
                            activeforeground=fg,
                            highlightthickness=0,
                            borderwidth=0
                        )
                    else:
                        widget.configure(
                            bg=button_bg, fg="#FFFFFF",
                            activebackground=button_active,
                            activeforeground="#FFFFFF",
                            highlightthickness=0,
                            borderwidth=0
                        )

                elif isinstance(widget, tk.Label):
                    if titlebar is not None and widget.master is titlebar:
                        widget.configure(bg=title_bg,fg=fg)
                    else:
                        widget.configure(bg=bg,fg=fg)

                elif isinstance(widget, tk.Frame):
                    if widget is titlebar:
                        widget.configure(bg=title_bg,bd=0,highlightthickness=0)
                    else:
                        widget.configure(bg=bg,bd=0,highlightthickness=0)

            except Exception:
                pass

            try:
                for child in widget.winfo_children():
                    paint(child)
            except Exception:
                pass

        paint(popup)

        # Ripristina la barra titolo dopo la ricorsione.
        # Deve restare GRIGIA anche in modalità giorno, mai bianca.
        if titlebar is not None:
            try:
                titlebar.configure(bg=title_bg,bd=0,highlightthickness=0)
                for child in titlebar.winfo_children():
                    try:
                        if isinstance(child,tk.Label):
                            child.configure(bg=title_bg,fg=fg)
                        elif isinstance(child,tk.Button):
                            child.configure(
                                bg=title_bg,fg=fg,
                                activebackground=border,
                                activeforeground=fg,
                                highlightthickness=0,
                                borderwidth=0
                            )
                    except Exception:
                        pass
            except Exception:
                pass

        try:
            popup.update_idletasks()
            popup.lift()
        except Exception:
            pass


    def _network_graph_reset_history(self):
        """Azzera la memoria usata esclusivamente dallo schema grafico di rete."""
        self._network_graph_history = {
            "routers": {},
            "clients": {},
            "lans": {},
            "cameras": {},
            # BSSID realmente usati come target di una cattura/scansione client.
            # Serve a distinguere nel grafico l'infrastruttura osservata da quella
            # effettivamente analizzata durante la sessione del programma.
            "captured_routers": set(),
        }
        self._network_graph_relations = []


    def _network_graph_ensure_history(self):
        hist = getattr(self, "_network_graph_history", None)
        if not isinstance(hist, dict):
            self._network_graph_reset_history()
            hist = self._network_graph_history
        for key in ("routers", "clients", "lans", "cameras"):
            if not isinstance(hist.get(key), dict):
                hist[key] = {}
        if not isinstance(hist.get("captured_routers"), set):
            try:
                hist["captured_routers"] = set(hist.get("captured_routers") or [])
            except Exception:
                hist["captured_routers"] = set()
        if not isinstance(getattr(self, "_network_graph_relations", None), list):
            self._network_graph_relations = []
        return hist



    def _ssid_for_scan_source(self, bssid):
        """Recupera l'SSID associato a un BSSID dalla GUI o dalla memoria sessione."""
        b = str(bssid or "").strip().lower()
        if not MAC_FULL.match(b):
            return ""

        try:
            cols = list(self.ap_tree["columns"])
            bi = cols.index("bssid")
            ei = cols.index("essid")
            for iid in self.ap_tree.get_children(""):
                vals = tuple(self.ap_tree.item(iid, "values") or ())
                if len(vals) > max(bi, ei) and str(vals[bi]).strip().lower() == b:
                    return str(vals[ei] or "").strip()
        except Exception:
            pass

        try:
            for vals in (getattr(self, "_dual_band_ap_snapshot", {}) or {}).values():
                vals = tuple(vals or ())
                if vals and str(vals[0]).strip().lower() == b:
                    return str(vals[3] if len(vals) > 3 else "").strip()
        except Exception:
            pass

        try:
            hist = self._network_graph_ensure_history()
            vals = tuple((hist.get("routers", {}) or {}).get(b, ()) or ())
            if vals:
                return str(vals[3] if len(vals) > 3 else "").strip()
        except Exception:
            pass
        return ""


    def _wifi_frequency_mhz_from_channel(self, channel):
        """Converte il canale Wi-Fi nella frequenza centrale nominale in MHz."""
        try:
            ch = int(float(str(channel).strip()))
        except Exception:
            return ""
        if 1 <= ch <= 13:
            return str(2407 + (5 * ch))
        if ch == 14:
            return "2484"
        if 32 <= ch <= 177:
            return str(5000 + (5 * ch))
        # Supporto nominale 6 GHz per eventuali estensioni future.
        if 1 <= ch <= 233:
            return "5935" if ch == 2 else str(5950 + (5 * ch))
        return ""

    def _scan_source_label(self, action_kind, bssid, channel, relation=""):
        """Etichetta leggibile che identifica da quale scansione proviene una riga."""
        action = str(action_kind or "").strip().lower()
        relation = str(relation or "").strip().lower()
        b = str(bssid or "").strip().lower()
        ch = str(channel or "").strip()
        ssid = self._ssid_for_scan_source(b) or "-"
        is_en = getattr(self, "language", "it") == "en"
        freq = self._wifi_frequency_mhz_from_channel(ch)
        freq_text = (f"{freq} MHz" if freq else (f"CH {ch}" if ch else "-"))
        try:
            ch_num = int(float(ch))
        except Exception:
            ch_num = 0
        if 1 <= ch_num <= 14:
            band_text = "2.4GHz"
        elif 32 <= ch_num <= 177:
            band_text = "5GHz"
        else:
            band_text = "-"

        if action == "client":
            # PROVENIENZA client: mostra la banda radio, non la frequenza in MHz
            # e non il numero di canale.
            label = f"{ssid} | {b.upper()} | {band_text}"
        else:
            # Nella provenienza della cattura non mostrare la parola
            # PASSIVA/PASSIVE: la sezione della GUI rende già evidente il tipo
            # di operazione. Manteniamo soltanto la relazione utile.
            if "cascade" in relation:
                head = "CASCADE" if is_en else "CASCATA"
            elif relation:
                head = "RELATED BAND" if is_en else "BANDA CORRELATA"
            else:
                head = ""

            # PROVENIENZA cattura/LAN: mostra la banda radio (2.4GHz/5GHz),
            # non il numero di canale.
            label = (
                f"{head} | {ssid} | {b.upper()} | {band_text}"
                if head else
                f"{ssid} | {b.upper()} | {band_text}"
            )

        try:
            if not isinstance(getattr(self, "_scan_source_bssid_map", None), dict):
                self._scan_source_bssid_map = {}
            self._scan_source_bssid_map[label] = b
        except Exception:
            pass
        return label


    def _scan_source_parent_bssid(self, label, fallback=""):
        try:
            b = str((getattr(self, "_scan_source_bssid_map", {}) or {}).get(
                str(label or ""), ""
            ) or "").strip().lower()
            if MAC_FULL.match(b):
                return b
        except Exception:
            pass
        f = str(fallback or "").strip().lower()
        return f if MAC_FULL.match(f) else ""


    def _prepare_correlated_passive_preservation(
        self,
        source_bssid,
        source_channel,
        target_bssid,
        target_channel,
        relation
    ):
        """Conserva VISIVAMENTE la cattura precedente prima di passare al nuovo BSSID.

        Lo stato analitico della nuova cattura riparte da zero; ciò che resta nella GUI
        è soltanto lo storico visivo, marcato con BSSID/SSID/canale di provenienza.
        """
        src_b = str(source_bssid or "").strip().lower()
        src_ch = str(source_channel or "").strip()
        dst_b = str(target_bssid or "").strip().lower()
        dst_ch = str(target_channel or "").strip()

        old_label = str(getattr(self, "_passive_current_source_label", "") or "").strip()
        if not old_label:
            old_label = self._scan_source_label("passive", src_b, src_ch, "")

        # Marca le righe MAC già visibili.
        try:
            for iid in self.res_tree.get_children(""):
                vals = list(self.res_tree.item(iid, "values") or ())
                while len(vals) < 6:
                    vals.append("")
                if not str(vals[5] or "").strip():
                    vals[5] = old_label
                    self.res_tree.item(iid, values=tuple(vals))
        except Exception:
            pass

        # Marca le righe LAN già visibili.
        try:
            for iid in self.lan_vendor_tree.get_children(""):
                vals = list(self.lan_vendor_tree.item(iid, "values") or ())
                while len(vals) < 6:
                    vals.append("")
                if not str(vals[5] or "").strip():
                    vals[5] = old_label
                    self.lan_vendor_tree.item(iid, values=tuple(vals))
        except Exception:
            pass

        # La tabella telecamere ha già PROVENIENZA: manteniamo la natura WIFI/LAN
        # e aggiungiamo il punto esatto della cattura.
        try:
            if not isinstance(getattr(self, "_camera_capture_sources", None), dict):
                self._camera_capture_sources = {}
            if not isinstance(getattr(self, "_camera_capture_bssids", None), dict):
                self._camera_capture_bssids = {}

            for iid in self.camera_tree.get_children(""):
                vals = list(self.camera_tree.item(iid, "values") or ())
                if not vals:
                    continue
                mac = str(vals[0] or "").replace("(*)", "").strip().lower()
                if not MAC_FULL.match(mac):
                    continue

                self._camera_capture_sources.setdefault(mac, set()).add(old_label)
                if MAC_FULL.match(src_b):
                    self._camera_capture_bssids.setdefault(mac, set()).add(src_b)

                while len(vals) < 7:
                    vals.append("")
                base = str(vals[5] or "").strip()
                # Elimina eventuali vecchie etichette duplicate dal testo visuale.
                nature = base.split(" | ", 1)[0].strip() or "LAN/WIFI"
                sources = sorted(self._camera_capture_sources.get(mac, set()))
                vals[5] = nature + (" | " + " ; ".join(sources) if sources else "")
                self.camera_tree.item(iid, values=tuple(vals))
        except Exception:
            pass

        # Nuova cattura correlata: le Treeview non devono essere svuotate.
        self._preserve_results_for_correlated_passive_scan = True
        self._passive_next_relation = str(relation or "correlation")
        self._passive_previous_source_label = old_label

        # Pre-registra anche l'etichetta del target; start_capture la renderà corrente.
        self._passive_next_source_label = self._scan_source_label(
            "passive", dst_b, dst_ch, relation
        )

        try:
            self._network_graph_snapshot_current(src_b, "before correlated passive scan")
        except Exception:
            pass


    def _camera_display_row_with_scan_source(self, mac, row):
        """Aggiunge la provenienza di cattura alla sola riga GUI della camera."""
        vals = list(tuple(row[:7]))
        while len(vals) < 7:
            vals.append("")

        source = str(getattr(self, "_passive_current_source_label", "") or "").strip()
        bssid = str(getattr(self, "_passive_current_source_bssid", "") or "").strip().lower()

        try:
            if not isinstance(getattr(self, "_camera_capture_sources", None), dict):
                self._camera_capture_sources = {}
            if not isinstance(getattr(self, "_camera_capture_bssids", None), dict):
                self._camera_capture_bssids = {}

            if source:
                self._camera_capture_sources.setdefault(mac, set()).add(source)
            if MAC_FULL.match(bssid):
                self._camera_capture_bssids.setdefault(mac, set()).add(bssid)

            base = str(vals[5] or "").strip()
            nature = base.split(" | ", 1)[0].strip() or "LAN/WIFI"
            sources = sorted(self._camera_capture_sources.get(mac, set()))
            vals[5] = nature + (" | " + " ; ".join(sources) if sources else "")
        except Exception:
            pass

        return tuple(vals)




    def _merge_camera_candidates_from_client_scan(self, rows, bssid="", channel=""):
        """Fallback prudente per camere Wi-Fi riconoscibili già nella scansione CLIENT.

        Non dichiara streaming: crea soltanto un candidato POSSIBILE quando
        l'identità vendor/OUI è fortemente orientata a telecamere.
        Serve soprattutto per dispositivi embedded/idle che possono non produrre
        DATA utile durante la successiva cattura passiva.
        """
        if not hasattr(self, "camera_tree"):
            return

        bssid = str(bssid or self._dual_band_value(getattr(self, "bssid", ""))).strip().lower()
        channel = str(channel or self._dual_band_value(getattr(self, "channel", ""))).strip()
        blocked = set(self._known_ap_bssids())
        if MAC_FULL.match(bssid):
            blocked.add(bssid)

        strong_words = (
            "trolink", "reolink", "hikvision", "dahua", "axis", "vivotek",
            "foscam", "ezviz", "imou", "arlo", "wyze", "ring", "blink",
            "amcrest", "wisenet", "hanwha", "swann", "lorex", "xiongmai",
            "instar", "mobotix", "avigilon", "geovision", "camera"
        )
        known_camera_ouis = {
            "30:4a:26": "Shenzhen Trolink Technology",
        }

        if not isinstance(getattr(self, "camera_candidate_rows", None), dict):
            self.camera_candidate_rows = {}
        if not isinstance(getattr(self, "camera_candidate_details", None), dict):
            self.camera_candidate_details = {}

        source_label = str(getattr(self, "_client_current_source_label", "") or "").strip()
        if not source_label:
            source_label = self._scan_source_label("client", bssid, channel, "")

        for row in rows or []:
            vals = tuple(row or ())
            if len(vals) < 5:
                continue

            mac = str(vals[0] or "").strip().lower()
            if not MAC_FULL.match(mac) or mac in blocked or self.is_multicast_or_broadcast(mac):
                continue

            try:
                locally_admin = bool(int(mac.split(":")[0], 16) & 0x02)
            except Exception:
                locally_admin = False
            if locally_admin:
                continue

            vendor = str(vals[2] if len(vals) > 2 else "").strip()
            if not vendor or vendor.lower() in ("unknown", "sconosciuto", "-", "n/a"):
                vendor = known_camera_ouis.get(mac[:8], "")
            if not vendor:
                try:
                    vendor = str(self.resolve_mac_with_manuf(mac) or "").strip()
                except Exception:
                    vendor = ""
            if not vendor or vendor.lower() in ("unknown", "sconosciuto", "mac locale/randomizzato"):
                vendor = known_camera_ouis.get(mac[:8], "")
            if not vendor:
                continue

            vlow = vendor.lower()
            identity_strong = (
                mac[:8] in known_camera_ouis
                or any(w in vlow for w in strong_words)
            )
            if not identity_strong:
                continue

            try:
                packets = int(float(str(vals[4] or "0").strip()))
            except Exception:
                packets = 0
            if packets < 3:
                continue

            score = 48 if ("trolink" in vlow or mac[:8] in known_camera_ouis) else 45
            level = "POSSIBLE" if getattr(self, "language", "it") == "en" else "POSSIBILE"
            txrx = "-"
            duration = "-"
            provenance = "WIFI CLIENT" if getattr(self, "language", "it") == "en" else "CLIENT WIFI"
            indicators = (
                f"camera-oriented identity observed as Wi-Fi client; {packets} frames; "
                f"no streaming claim; source {source_label}"
                if getattr(self, "language", "it") == "en"
                else
                f"identità orientata a telecamera osservata come client Wi-Fi; {packets} frame; "
                f"nessuna affermazione di streaming; sorgente {source_label}"
            )

            out_row = (
                mac, vendor, f"{score}/100", level,
                txrx, provenance, duration, indicators
            )

            old = self.camera_candidate_rows.get(mac)
            old_det = self.camera_candidate_details.get(mac, {}) or {}
            try:
                old_score = int(str(old[2]).split("/", 1)[0]) if old else -1
            except Exception:
                old_score = -1

            if score >= old_score:
                self.camera_candidate_rows[mac] = out_row
                self.camera_candidate_details[mac] = {
                    "mac": mac,
                    "vendor": vendor,
                    "score": score,
                    "level": level,
                    "class": "WIFI",
                    "provenance": "WIFI",
                    "client_identity_candidate": True,
                    "cascade_parent_bssid": bssid,
                    "source_label": source_label,
                    "frames": packets,
                    "reasons": [
                        (
                            "Camera-oriented vendor/OUI observed as an associated Wi-Fi client."
                            if getattr(self, "language", "it") == "en"
                            else
                            "Vendor/OUI orientato a telecamera osservato come client Wi-Fi associato."
                        ),
                        (
                            "Traffic profile not available: candidate kept only as POSSIBLE."
                            if getattr(self, "language", "it") == "en"
                            else
                            "Profilo di traffico non disponibile: candidato mantenuto solo come POSSIBILE."
                        ),
                    ],
                    "traffic_profile": "CLIENT IDENTITY ONLY",
                }

                display = self._camera_display_row_with_scan_source(mac, out_row)
                if self.camera_tree.exists(mac):
                    self.camera_tree.item(mac, values=display)
                else:
                    self.camera_tree.insert("", "end", iid=mac, values=display)

        try:
            self.camera_number_text.set(
                ("Count: " if getattr(self, "language", "it") == "en" else "Numero: ")
                + str(len(self.camera_tree.get_children()))
            )
            self._refresh_camera_block_action()
        except Exception:
            pass



    def _network_graph_snapshot_current(self, parent_bssid=None, source=""):
        """Conserva i risultati visibili associandoli al BSSID che li ha prodotti.

        Serve solo allo schema grafico. In una seconda scansione le tabelle della GUI
        possono essere pulite/riutilizzate; questa memoria permette all'esportazione di
        mostrare insieme prima e seconda scansione senza cambiare gli algoritmi di analisi.
        """
        hist = self._network_graph_ensure_history()

        def _norm_mac(value):
            s = str(value or "").replace("(*)", "").strip().lower()
            return s if MAC_FULL.match(s) else ""

        def _rows(tree_name):
            out = []
            tree = getattr(self, tree_name, None)
            if tree is None:
                return out
            try:
                for iid in tree.get_children(""):
                    vals = tuple(tree.item(iid, "values") or ())
                    if vals:
                        out.append(vals)
            except Exception:
                pass
            return out

        parent = _norm_mac(parent_bssid)
        if not parent:
            try:
                parent = _norm_mac(self._dual_band_value(getattr(self, "bssid", "")))
            except Exception:
                parent = ""

        # I router vengono sempre presi tutti dalla scansione multicanale.
        for row in _rows("ap_tree"):
            bssid = _norm_mac(row[0] if len(row) > 0 else "")
            if bssid:
                hist["routers"][bssid] = tuple(row)

        if not parent:
            return

        try:
            hist.setdefault("captured_routers", set()).add(parent)
        except Exception:
            pass

        # Se il target corrente non e' piu' nella scansione router visibile,
        # mantienilo comunque come nodo infrastrutturale della sessione.
        if parent not in hist["routers"]:
            _found_parent_row = None
            try:
                for _vals in (getattr(self, "_dual_band_ap_snapshot", {}) or {}).values():
                    _vals = tuple(_vals or ())
                    if _vals and _norm_mac(_vals[0]) == parent:
                        _found_parent_row = _vals
                        break
            except Exception:
                pass
            hist["routers"][parent] = tuple(_found_parent_row or (parent, "", "", "Router / BSSID", "", "", "", ""))

        # CLIENT: ogni riga porta ora la propria provenienza. In una scansione
        # correlata le righe precedenti restano visibili senza essere attribuite
        # artificialmente al nuovo BSSID.
        for row in _rows("client_tree"):
            mac = _norm_mac(row[0] if len(row) > 0 else "")
            if not mac:
                continue
            src = str(row[6] if len(row) > 6 else "")
            use_parent = self._scan_source_parent_bssid(src, parent) or parent
            hist["clients"][(use_parent, mac)] = tuple(row)

        # LAN: stessa regola; la sesta colonna identifica il segmento passivo.
        for row in _rows("lan_vendor_tree"):
            mac = _norm_mac(row[4] if len(row) > 4 else "")
            if not mac:
                continue
            src = str(row[5] if len(row) > 5 else "")
            use_parent = self._scan_source_parent_bssid(src, "")
            if not use_parent:
                existing = [k for k in hist["lans"] if k[1] == mac]
                use_parent = existing[0][0] if existing else parent
            hist["lans"][(use_parent, mac)] = tuple(row)

        # TELECAMERE: usa prima l'eventuale parent esplicito creato dalla seconda
        # scansione cascata. I placeholder infrastrutturali non sono dispositivi reali
        # e non devono finire nello schema.
        details_map = getattr(self, "camera_candidate_details", {}) or {}
        known_aps = set()
        try:
            known_aps = set(self._known_ap_bssids())
        except Exception:
            known_aps = set(hist["routers"].keys())

        for row in _rows("camera_tree"):
            mac = _norm_mac(row[0] if len(row) > 0 else "")
            vendor = str(row[1] if len(row) > 1 else "")
            if not mac or mac in known_aps:
                continue
            try:
                if self._is_camera_infrastructure_mac(mac, vendor):
                    # Pulisce anche una eventuale vecchia entry gia' storicizzata.
                    for _k in [k for k in list(hist["cameras"].keys()) if k[1] == mac]:
                        hist["cameras"].pop(_k, None)
                    continue
            except Exception:
                pass
            det = details_map.get(mac, {}) or {}
            if det.get("cascade_camera_candidate") or str(det.get("class", "")).upper() == "CASCADE ROUTER":
                continue

            explicit_parent = _norm_mac(
                det.get("router_cam_parent_bssid")
                or det.get("cascade_parent_bssid")
                or det.get("capture_bssid")
                or ""
            )
            capture_parents = set()
            try:
                capture_parents = {
                    _norm_mac(_p)
                    for _p in (getattr(self, "_camera_capture_bssids", {}) or {}).get(mac, set())
                    if _norm_mac(_p)
                }
            except Exception:
                capture_parents = set()

            if explicit_parent:
                capture_parents.add(explicit_parent)

            if capture_parents:
                for use_parent in sorted(capture_parents):
                    hist["cameras"][(use_parent, mac)] = tuple(row)
            else:
                existing = [k for k in hist["cameras"] if k[1] == mac]
                use_parent = existing[0][0] if existing else parent
                hist["cameras"][(use_parent, mac)] = tuple(row)

        try:
            self.command_debug_write(
                f"[GRAPH] snapshot {source or 'current'} -> BSSID {parent} | "
                f"R={len(hist['routers'])} C={len(hist['clients'])} "
                f"L={len(hist['lans'])} CAM={len(hist['cameras'])}"
            )
        except Exception:
            pass


    def _network_graph_register_dual_band(self, bssid_a, bssid_b):
        """Registra che due BSSID appartengono alle due radio correlate dello stesso router."""
        self._network_graph_ensure_history()
        a = str(bssid_a or "").strip().lower()
        b = str(bssid_b or "").strip().lower()
        if not MAC_FULL.match(a) or not MAC_FULL.match(b) or a == b:
            return
        rel = {"kind": "dual_band", "a": a, "b": b}
        for old in self._network_graph_relations:
            if old.get("kind") == "dual_band" and {old.get("a"), old.get("b")} == {a, b}:
                return
        self._network_graph_relations.append(rel)


    def _network_graph_register_cascade(self, parent_bssid, wan_mac, child_bssid):
        """Registra la topologia AP principale -> MAC WAN/LAN -> BSSID router in cascata."""
        self._network_graph_ensure_history()
        p = str(parent_bssid or "").strip().lower()
        w = str(wan_mac or "").strip().lower()
        c = str(child_bssid or "").strip().lower()
        if not MAC_FULL.match(p) or not MAC_FULL.match(c):
            return
        rel = {
            "kind": "cascade",
            "parent": p,
            "wan": w if MAC_FULL.match(w) else "",
            "child": c,
        }
        for old in self._network_graph_relations:
            if (old.get("kind") == "cascade"
                    and old.get("parent") == p
                    and old.get("child") == c
                    and old.get("wan", "") == rel["wan"]):
                return
        self._network_graph_relations.append(rel)


    def _network_graph_export_records(self):
        """Restituisce l'unione tra memoria multi-scansione e stato GUI corrente."""
        try:
            current_parent = self._dual_band_value(getattr(self, "bssid", ""))
        except Exception:
            current_parent = ""
        self._network_graph_snapshot_current(current_parent, "export")
        hist = self._network_graph_ensure_history()

        routers = list(hist["routers"].values())
        clients = [
            {"parent": p, "mac": m, "row": row}
            for (p, m), row in hist["clients"].items()
        ]
        lans = [
            {"parent": p, "mac": m, "row": row}
            for (p, m), row in hist["lans"].items()
        ]
        # Ultimo filtro difensivo: un router/AP non deve riapparire nel grafico
        # a causa di una vecchia snapshot della stessa sessione.
        for _k, _row in list(hist["cameras"].items()):
            try:
                _m = _k[1]
                _v = str(_row[1] if len(_row) > 1 else "")
                if self._is_camera_infrastructure_mac(_m, _v):
                    hist["cameras"].pop(_k, None)
            except Exception:
                pass
        cameras = [
            {"parent": p, "mac": m, "row": row}
            for (p, m), row in hist["cameras"].items()
        ]
        return routers, clients, lans, cameras, list(self._network_graph_relations)




    def _network_graph_build_topology_model(self, routers, clients, lans, cameras, relations, selected_bssid=""):
        """Costruisce una topologia fisica leggibile per il grafico.

        - Le radio dual-band dello stesso access point vengono raggruppate in UN nodo.
        - I collegamenti AP/router a valle vengono ricavati prima dalle relazioni
          esplicite della doppia scansione e, se mancanti, dalla correlazione forte
          MAC LAN <-> BSSID (stesso OUI + MAC vicini).
        - Ogni access point a valle ha un solo padre nel grafico, scegliendo la
          correlazione piu' forte. Nessuna relazione viene inventata dal solo SSID.
        """
        def clean(v):
            s = str(v or "").replace("(*)", "").strip().lower()
            return s if MAC_FULL.match(s) else ""

        def band_from_ch(v):
            try:
                ch = int(float(str(v).strip()))
            except Exception:
                return ""
            if 1 <= ch <= 14:
                return "2.4"
            if 32 <= ch <= 177:
                return "5"
            return ""

        router_map = {}
        raw_order = []
        for row in routers or []:
            row = tuple(row or ())
            b = clean(row[0] if row else "")
            if not b:
                continue
            router_map[b] = row
            if b not in raw_order:
                raw_order.append(b)

        # Ogni parent o BSSID citato dalle relazioni deve esistere nel modello.
        extras = []
        for rec in list(clients or []) + list(lans or []) + list(cameras or []):
            p = clean(rec.get("parent", ""))
            if p:
                extras.append(p)
        for rel in relations or []:
            for k in ("parent", "child", "a", "b"):
                m = clean(rel.get(k, ""))
                if m:
                    extras.append(m)
        if clean(selected_bssid):
            extras.append(clean(selected_bssid))
        for b in extras:
            if b not in router_map:
                router_map[b] = (b, "", "", "Router / BSSID", "", "", "", "")
                raw_order.append(b)

        # Union-find per radio dual-band. La relazione viene accettata soltanto
        # se e' ancora coerente con OUI, banda e SSID/distanza MAC.
        uf = {b: b for b in raw_order}
        def find(x):
            while uf.get(x, x) != x:
                uf[x] = uf.get(uf[x], uf[x])
                x = uf[x]
            return x
        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                ia = raw_order.index(ra) if ra in raw_order else 10**9
                ib = raw_order.index(rb) if rb in raw_order else 10**9
                if ia <= ib:
                    uf[rb] = ra
                else:
                    uf[ra] = rb

        accepted_dual = []
        for rel in relations or []:
            if str(rel.get("kind", "")) != "dual_band":
                continue
            a, b = clean(rel.get("a", "")), clean(rel.get("b", ""))
            if not a or not b or a not in router_map or b not in router_map or a == b:
                continue
            ra, rb = router_map[a], router_map[b]
            cha = str(ra[1] if len(ra) > 1 else "")
            chb = str(rb[1] if len(rb) > 1 else "")
            ba, bb = band_from_ch(cha), band_from_ch(chb)
            sa = str(ra[3] if len(ra) > 3 else "").strip().casefold()
            sb = str(rb[3] if len(rb) > 3 else "").strip().casefold()
            same_ssid = bool(sa and sb and sa == sb)
            same_oui = a[:8] == b[:8]
            try:
                dist = abs(int(a.replace(":", ""), 16) - int(b.replace(":", ""), 16))
            except Exception:
                dist = 10**12
            middle4 = a.split(":")[1:5] == b.split(":")[1:5]
            if ba and bb and ba != bb and same_oui and middle4 and (same_ssid or dist <= 32):
                union(a, b)
                accepted_dual.append((a, b))

        groups = {}
        group_of = {}
        for b in raw_order:
            r = find(b)
            groups.setdefault(r, []).append(b)
        # Dopo le union la radice puo' cambiare: normalizza.
        normalized = {}
        for members in groups.values():
            root = min(members, key=lambda x: raw_order.index(x) if x in raw_order else 10**9)
            normalized[root] = list(members)
            for m in members:
                group_of[m] = root
        groups = normalized

        captured = set()
        try:
            captured = set((getattr(self, "_network_graph_history", {}) or {}).get("captured_routers", set()) or set())
        except Exception:
            pass

        def radio_info(b):
            row = router_map.get(b, (b, "", "", "Router", "", "", "", ""))
            ch = str(row[1] if len(row) > 1 else "")
            pwr = str(row[2] if len(row) > 2 else "")
            essid = str(row[3] if len(row) > 3 else "").strip() or "Router / BSSID"
            band = str(row[4] if len(row) > 4 else "").strip() or band_from_ch(ch)
            return {"bssid": b, "ch": ch, "pwr": pwr, "essid": essid, "band": band}

        group_info = {}
        for gid, members in groups.items():
            radios = [radio_info(m) for m in members]
            radios.sort(key=lambda r: (0 if str(r.get("band", "")).startswith("2.4") else 1 if str(r.get("band", "")).startswith("5") else 2,
                                       int(r["ch"]) if str(r.get("ch", "")).isdigit() else 999,
                                       r["bssid"]))
            names = [r["essid"] for r in radios if r["essid"] and r["essid"] != "Router / BSSID"]
            name = names[0] if names else "Router / Access Point"
            group_info[gid] = {
                "id": gid,
                "members": members,
                "radios": radios,
                "name": name,
                "dual": len(radios) > 1,
                "captured": any(m in captured for m in members),
                "selected": clean(selected_bssid) in members,
            }

        # Reindirizza dispositivi dalla singola radio al nodo fisico AP/router.
        def group_records(records):
            out = {g: [] for g in groups}
            fallback_b = clean(selected_bssid) or (raw_order[0] if raw_order else "")
            fallback_g = group_of.get(fallback_b, fallback_b)
            for rec in records or []:
                p = clean(rec.get("parent", "")) or fallback_b
                g = group_of.get(p, fallback_g)
                if not g:
                    continue
                out.setdefault(g, []).append(rec)
            return out

        by_client = group_records(clients)
        by_lan = group_records(lans)
        by_cam = group_records(cameras)

        # Relazioni esplicite di cascata: priorita' massima.
        edge_candidates = []
        explicit_children = set()
        for rel in relations or []:
            if str(rel.get("kind", "")) != "cascade":
                continue
            p, c = clean(rel.get("parent", "")), clean(rel.get("child", ""))
            if not p or not c:
                continue
            gp, gc = group_of.get(p, p), group_of.get(c, c)
            if not gp or not gc or gp == gc:
                continue
            edge_candidates.append({
                "parent": gp, "child": gc, "wan": clean(rel.get("wan", "")),
                "kind": "cascade", "score": 100, "distance": 0,
            })
            explicit_children.add(gc)

        # Se la doppia scansione non e' stata accettata, il grafico puo' comunque
        # mostrare un collegamento AP probabile quando la PRIMA cattura ha visto
        # un MAC LAN quasi identico al BSSID di un AP rilevato. E' la firma tipica
        # WAN/LAN <-> radio dello stesso apparato. Stesso OUI e distanza stretta
        # sono obbligatori: il solo SSID non crea mai una freccia.
        inferred_by_child = {}
        known_bssids = set(router_map)
        for rec in lans or []:
            lp = clean(rec.get("parent", ""))
            lm = clean(rec.get("mac", ""))
            if not lp or not lm or lm in known_bssids:
                continue
            gp = group_of.get(lp, lp)
            if not gp:
                continue
            try:
                lmi = int(lm.replace(":", ""), 16)
            except Exception:
                continue
            for b in raw_order:
                gc = group_of.get(b, b)
                if not gc or gc == gp or gc in explicit_children:
                    continue
                if lm[:8] != b[:8]:
                    continue
                try:
                    dist = abs(lmi - int(b.replace(":", ""), 16))
                except Exception:
                    continue
                middle4 = lm.split(":")[1:5] == b.split(":")[1:5]
                if dist <= 4:
                    score = 94
                elif dist <= 16:
                    score = 88
                elif dist <= 32:
                    score = 82
                elif dist <= 64:
                    score = 74
                elif dist <= 256 and middle4:
                    score = 66
                else:
                    continue
                cand = {
                    "parent": gp, "child": gc, "wan": lm,
                    "child_bssid": b, "kind": "cascade_inferred",
                    "score": score, "distance": dist,
                }
                old = inferred_by_child.get(gc)
                if old is None or (score, -dist) > (old["score"], -old["distance"]):
                    inferred_by_child[gc] = cand

        edge_candidates.extend(inferred_by_child.values())

        # Un solo padre per AP/router a valle. Esplicito > inferito; poi score.
        chosen = {}
        for e in edge_candidates:
            c = e["child"]
            old = chosen.get(c)
            rank = (1 if e["kind"] == "cascade" else 0, int(e.get("score", 0)))
            oldrank = (-1, -1) if old is None else (1 if old["kind"] == "cascade" else 0, int(old.get("score", 0)))
            if old is None or rank > oldrank:
                chosen[c] = e
        edges = list(chosen.values())

        children = {}
        incoming = set()
        for e in edges:
            children.setdefault(e["parent"], []).append(e["child"])
            incoming.add(e["child"])

        # Ordine: prima radici con catture e relazioni in uscita, poi i figli.
        roots = [g for g in groups if g not in incoming]
        roots.sort(key=lambda g: (
            0 if group_info[g]["captured"] else 1,
            -len(children.get(g, [])),
            raw_order.index(group_info[g]["members"][0]) if group_info[g]["members"][0] in raw_order else 10**9
        ))
        order = []
        seen = set()
        def walk(g):
            if g in seen:
                return
            seen.add(g); order.append(g)
            kids = children.get(g, [])
            kids.sort(key=lambda x: raw_order.index(group_info[x]["members"][0]) if group_info[x]["members"][0] in raw_order else 10**9)
            for k in kids:
                walk(k)
        for g in roots:
            walk(g)
        for g in groups:
            walk(g)

        return {
            "router_map": router_map,
            "groups": group_info,
            "group_of": group_of,
            "order": order,
            "by_client": by_client,
            "by_lan": by_lan,
            "by_cam": by_cam,
            "edges": edges,
            "accepted_dual": accepted_dual,
        }


    def export_network_diagram_svg(self):
        """Esporta un grafico unico della sessione con topologia fisica, pan e zoom."""
        from html import escape as _xml_escape

        en = getattr(self, "language", "it") == "en"
        routers, clients, lans, cameras, relations = self._network_graph_export_records()
        if not routers and not clients and not lans and not cameras:
            try:
                messagebox.showwarning(
                    "EXPORT GRAPH" if en else "ESPORTA GRAFICO",
                    "No detected devices to export." if en else "Nessun dispositivo rilevato da esportare."
                )
            except Exception:
                pass
            return

        def clean(v):
            s = str(v or "").replace("(*)", "").strip().lower()
            return s if MAC_FULL.match(s) else ""

        def clip(v, n):
            s = str(v or "").strip()
            return s if len(s) <= n else s[:max(1, n-1)] + "…"

        try:
            selected_bssid = clean(self._dual_band_value(getattr(self, "bssid", "")))
        except Exception:
            selected_bssid = ""

        model = self._network_graph_build_topology_model(
            routers, clients, lans, cameras, relations, selected_bssid
        )
        groups = model["groups"]
        order = model["order"]
        by_client = model["by_client"]
        by_lan = model["by_lan"]
        by_cam = model["by_cam"]
        edges = model["edges"]

        WIDTH = 1750
        LEFT = 180                    # corsia relazioni: nessuna freccia passa sui box
        SECTION_W = 1530
        ROUTER_X, ROUTER_W = 220, 330
        CLIENT_X, CLIENT_W = 610, 315
        LAN_X, LAN_W = 980, 315
        CAM_X, CAM_W = 1350, 315
        CARD_H, CARD_GAP = 62, 14
        JOIN_GAP = 20

        # Riquadro relazioni in alto: rende esplicito il significato di ogni freccia.
        dual_groups = [g for g in order if len(groups[g]["radios"]) > 1]
        relation_lines = len(edges) + len(dual_groups)
        relation_h = 0 if relation_lines == 0 else 60 + 32 * relation_lines
        top = 132 + relation_h

        sections = []
        y = top
        for g in order:
            n = max(1, len(by_client.get(g, [])), len(by_lan.get(g, [])), len(by_cam.get(g, [])))
            router_card_h = 72 + 24 * len(groups[g]["radios"])
            h = max(210, 126 + n * (CARD_H + CARD_GAP), router_card_h + 100)
            sections.append({"group": g, "y": y, "h": h, "center": y + h/2, "router_card_h": router_card_h})
            y += h + 24
        HEIGHT = max(820, y + 78)
        secpos = {s["group"]: s for s in sections}

        graph_dark = bool(getattr(self, "night_mode", False))
        if graph_dark:
            bg = "#0B0F13"
            panel = "#11171D"
            panel_shadow = "#050709"
            header_fill = "#182129"
            grid_line = "#34424D"
            line = "#78909C"
            router_fill = "#172A3A"
            client_fill = "#173024"
            lan_fill = "#332A16"
            camera_fill = "#2D1F35"
            text = "#E7EEF3"
            muted = "#AAB8C2"
            accent = "#42A5F5"
            cascade = "#D69A6A"
            inferred = "#FFB74D"
            dual = "#CE93D8"
            border = "#41515D"
            divider = "#33414B"
            empty_fill = "#0E1419"
            empty_border = "#46545E"
            client_border = "#4E8060"
            lan_border = "#8D7542"
            camera_border = "#785A83"
            router_border = "#627D90"
            relation_fill = "#10161B"
            relation_border = "#44535E"
            label_bg = "#151C22"
        else:
            bg = "#EAF1F5"
            panel = "#FFFFFF"
            panel_shadow = "#D7E0E8"
            header_fill = "#F5F8FA"
            grid_line = "#D4DEE6"
            line = "#617D8A"
            router_fill = "#DCEBFF"
            client_fill = "#E5F5EA"
            lan_fill = "#FFF1D3"
            camera_fill = "#F3E4F7"
            text = "#15212A"
            muted = "#53636E"
            accent = "#1565C0"
            cascade = "#8D5A3B"
            inferred = "#D97706"
            dual = "#7B1FA2"
            border = "#CBD7DF"
            divider = "#D7E1E8"
            empty_fill = "#FBFCFD"
            empty_border = "#CFD8DC"
            client_border = "#9FB7A5"
            lan_border = "#C7A968"
            camera_border = "#B29ABD"
            router_border = "#8EA6B7"
            relation_fill = "#F9FBFC"
            relation_border = "#B8C5CD"
            label_bg = "#FFFFFF"

        svg = []
        A = svg.append
        A(f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}" height="{HEIGHT}" viewBox="0 0 {WIDTH} {HEIGHT}">')
        A(f'<defs><marker id="arrCascade" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto"><path d="M0,0 L0,6 L9,3 z" fill="{cascade}"/></marker><marker id="arrInfer" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto"><path d="M0,0 L0,6 L9,3 z" fill="{inferred}"/></marker></defs>')
        A(f'<rect width="100%" height="100%" fill="{bg}"/>')
        A('<style>text{font-family:Arial,Helvetica,sans-serif}.title{font-size:28px;font-weight:700}.sub{font-size:14px}.head{font-size:14px;font-weight:700}.name{font-size:15px;font-weight:700}.small{font-size:12px}.mac{font-family:monospace;font-size:12.5px;font-weight:700}.tiny{font-size:11px}.badge{font-size:10px;font-weight:700}</style>')

        title = "SESSION NETWORK TOPOLOGY" if en else "TOPOLOGIA DI RETE DELLA SESSIONE"
        stamp_now = datetime.now().strftime("%d/%m/%Y %H:%M:%S")
        summary = (
            f"Physical routers/APs {len(order)} • Wi-Fi clients {len(clients)} • LAN candidates {len(lans)} • Possible cameras {len(cameras)}"
            if en else
            f"Router/AP fisici {len(order)} • Client Wi-Fi {len(clients)} • Possibili LAN {len(lans)} • Possibili telecamere {len(cameras)}"
        )
        A(f'<text x="42" y="42" class="title" fill="{text}">{_xml_escape(title)}</text>')
        A(f'<text x="42" y="70" class="sub" fill="{muted}">{_xml_escape(summary)}</text>')
        A(f'<text x="42" y="94" class="small" fill="{muted}">{_xml_escape(stamp_now)}</text>')

        def group_name(g):
            return groups.get(g, {}).get("name", g)

        if relation_lines:
            rh = relation_h - 14
            A(f'<rect x="42" y="112" width="1666" height="{rh}" rx="14" fill="{relation_fill}" stroke="{relation_border}" stroke-width="1.3"/>')
            A(f'<text x="60" y="139" class="head" fill="{text}">{"TOPOLOGY RELATIONSHIPS" if en else "RELAZIONI TOPOLOGICHE"}</text>')
            ry = 166
            for g in dual_groups:
                radios = groups[g]["radios"]
                desc = "  ↔  ".join(f'{r.get("band") or "?"} GHz {r["bssid"].upper()} CH {r.get("ch") or "-"}' for r in radios)
                label = (f"SAME ACCESS POINT / DUAL BAND: {group_name(g)} — {desc}" if en
                         else f"STESSO ACCESS POINT / DOPPIA BANDA: {group_name(g)} — {desc}")
                A(f'<line x1="62" y1="{ry-5}" x2="98" y2="{ry-5}" stroke="{dual}" stroke-width="4" stroke-dasharray="5 4"/>')
                A(f'<text x="112" y="{ry}" class="small" fill="{text}">{_xml_escape(label)}</text>')
                ry += 32
            for e in edges:
                p, c = e["parent"], e["child"]
                if e["kind"] == "cascade":
                    col, dash = cascade, ""
                    prefix = "CASCADE / DOWNSTREAM AP" if en else "CASCATA / ACCESS POINT A VALLE"
                else:
                    col, dash = inferred, ' stroke-dasharray="7 5"'
                    prefix = "PROBABLE AP LINK" if en else "COLLEGAMENTO AP PROBABILE"
                via = f' — LAN/WAN {e.get("wan", "").upper()}' if e.get("wan") else ""
                score = f' — {e.get("score")}/100' if e["kind"] != "cascade" else ""
                label = f'{prefix}: {group_name(p)} → {group_name(c)}{via}{score}'
                A(f'<line x1="62" y1="{ry-5}" x2="98" y2="{ry-5}" stroke="{col}" stroke-width="4"{dash}/>' )
                A(f'<text x="112" y="{ry}" class="small" fill="{text}">{_xml_escape(label)}</text>')
                ry += 32

        incoming = {e["child"] for e in edges}
        outgoing = {e["parent"] for e in edges}

        def add_card(x, yy, w, h, fillc, strokec, sw=1.2):
            A(f'<rect x="{x+3}" y="{yy+4}" width="{w}" height="{h}" rx="11" fill="#000" opacity="0.05"/>')
            A(f'<rect x="{x}" y="{yy}" width="{w}" height="{h}" rx="11" fill="{fillc}" stroke="{strokec}" stroke-width="{sw}"/>')

        def connector(router_x, router_y, bus_y, join_x, target_x, target_y, dashed=False):
            dash = ' stroke-dasharray="7 5"' if dashed else ""
            ex = router_x + 14
            A(f'<path d="M{router_x} {router_y} L{ex} {router_y} L{ex} {bus_y} L{join_x} {bus_y} L{join_x} {target_y} L{target_x} {target_y}" fill="none" stroke="{line}" stroke-width="1.9"{dash}/>' )

        for idx, sec in enumerate(sections, 1):
            g, sy, sh = sec["group"], sec["y"], sec["h"]
            gi = groups[g]
            A(f'<rect x="{LEFT+4}" y="{sy+5}" width="{SECTION_W}" height="{sh}" rx="18" fill="#000" opacity="0.05"/>')
            A(f'<rect x="{LEFT}" y="{sy}" width="{SECTION_W}" height="{sh}" rx="18" fill="{panel}" stroke="{border}" stroke-width="1.4"/>')
            A(f'<rect x="{LEFT}" y="{sy}" width="{SECTION_W}" height="44" rx="18" fill="{header_fill}"/>')
            A(f'<line x1="{LEFT}" y1="{sy+44}" x2="{LEFT+SECTION_W}" y2="{sy+44}" stroke="{divider}"/>')

            role = ("MAIN ROUTER" if en else "ROUTER PRINCIPALE") if g not in incoming and g in outgoing else \
                   (("DOWNSTREAM AP / ROUTER" if en else "ACCESS POINT / ROUTER A VALLE") if g in incoming else \
                    ("ROUTER / ACCESS POINT" if en else "ROUTER / ACCESS POINT"))
            A(f'<text x="{ROUTER_X}" y="{sy+28}" class="head" fill="{muted}">{_xml_escape(role)} {idx}</text>')
            A(f'<text x="{CLIENT_X}" y="{sy+28}" class="head" fill="{muted}">{"WI-FI CLIENTS" if en else "CLIENT WIFI"} ({len(by_client.get(g, []))})</text>')
            A(f'<text x="{LAN_X}" y="{sy+28}" class="head" fill="{muted}">{"LAN CANDIDATES" if en else "POSSIBILI LAN"} ({len(by_lan.get(g, []))})</text>')
            A(f'<text x="{CAM_X}" y="{sy+28}" class="head" fill="{muted}">{"POSSIBLE CAMERAS" if en else "POSSIBILI TELECAMERE"} ({len(by_cam.get(g, []))})</text>')

            router_y = sy + 68
            router_h = sec["router_card_h"]
            selected = gi.get("selected", False)
            add_card(ROUTER_X, router_y, ROUTER_W, router_h, router_fill, accent if selected else router_border, 3 if selected else 1.4)
            A(f'<text x="{ROUTER_X+14}" y="{router_y+24}" class="name" fill="{text}">{_xml_escape(clip(gi["name"], 30))}</text>')
            badge = []
            if gi.get("captured"):
                badge.append("CATTURATO" if not en else "CAPTURED")
            if gi.get("dual"):
                badge.append("DOPPIA BANDA" if not en else "DUAL BAND")
            if badge:
                A(f'<text x="{ROUTER_X+14}" y="{router_y+43}" class="badge" fill="{accent}">{_xml_escape(" • ".join(badge))}</text>')
            basey = router_y + 64
            for r in gi["radios"]:
                band = str(r.get("band") or "?")
                if band and "GHz" not in band:
                    band += " GHz"
                line_txt = f'{band}  {r["bssid"].upper()}  CH {r.get("ch") or "-"}'
                A(f'<text x="{ROUTER_X+14}" y="{basey}" class="mac" fill="{text}">{_xml_escape(line_txt)}</text>')
                basey += 24

            bus_y = sy + 54
            anchor_x = ROUTER_X + ROUTER_W
            anchor_y = router_y + router_h/2
            for x in (CLIENT_X-JOIN_GAP, LAN_X-JOIN_GAP, CAM_X-JOIN_GAP):
                A(f'<line x1="{x}" y1="{bus_y}" x2="{x}" y2="{sy+sh-24}" stroke="{grid_line}" stroke-dasharray="3 6"/>')

            def empty_box(x, w, label):
                ey = sy + 78
                A(f'<rect x="{x}" y="{ey}" width="{w}" height="54" rx="10" fill="{empty_fill}" stroke="{empty_border}" stroke-dasharray="5 4"/>')
                A(f'<text x="{x+w/2}" y="{ey+32}" class="small" text-anchor="middle" fill="{muted}">{_xml_escape(label)}</text>')

            items = by_client.get(g, [])
            if not items:
                empty_box(CLIENT_X, CLIENT_W, "No Wi-Fi clients" if en else "Nessun client Wi-Fi")
            for i, rec in enumerate(items):
                row = tuple(rec.get("row", ()) or ())
                cy = sy + 70 + i*(CARD_H+CARD_GAP); center = cy + CARD_H/2
                mac = str(row[0]) if len(row)>0 else rec.get("mac", "")
                name = str(row[1]) if len(row)>1 else ""
                vendor = str(row[2]) if len(row)>2 else ""
                pwr = str(row[3]) if len(row)>3 else ""
                name = name or vendor or ("Wi-Fi client" if en else "Client Wi-Fi")
                connector(anchor_x, anchor_y, bus_y, CLIENT_X-JOIN_GAP, CLIENT_X, center, False)
                add_card(CLIENT_X, cy, CLIENT_W, CARD_H, client_fill, client_border)
                A(f'<text x="{CLIENT_X+11}" y="{cy+21}" class="name" fill="{text}">{_xml_escape(clip(name, 27))}</text>')
                A(f'<text x="{CLIENT_X+11}" y="{cy+42}" class="mac" fill="{text}">{_xml_escape(mac)}</text>')
                tail = vendor if vendor and vendor != name else ""
                if pwr: tail += ((" • " if tail else "") + "PWR " + pwr)
                A(f'<text x="{CLIENT_X+11}" y="{cy+56}" class="tiny" fill="{muted}">{_xml_escape(clip(tail, 39))}</text>')

            items = by_lan.get(g, [])
            if not items:
                empty_box(LAN_X, LAN_W, "No LAN candidates" if en else "Nessun candidato LAN")
            for i, rec in enumerate(items):
                row = tuple(rec.get("row", ()) or ())
                cy = sy + 70 + i*(CARD_H+CARD_GAP); center = cy + CARD_H/2
                vendor = str(row[0]) if len(row)>0 else ""
                role2 = str(row[1]) if len(row)>1 else ""
                level = str(row[2]) if len(row)>2 else ""
                mac = str(row[4]) if len(row)>4 else rec.get("mac", "")
                name = role2 or vendor or ("LAN candidate" if en else "Candidato LAN")
                connector(anchor_x, anchor_y, bus_y, LAN_X-JOIN_GAP, LAN_X, center, True)
                add_card(LAN_X, cy, LAN_W, CARD_H, lan_fill, lan_border)
                A(f'<text x="{LAN_X+11}" y="{cy+21}" class="name" fill="{text}">{_xml_escape(clip(name, 27))}</text>')
                A(f'<text x="{LAN_X+11}" y="{cy+42}" class="mac" fill="{text}">{_xml_escape(mac)}</text>')
                tail = vendor + ((" • "+level) if level else "")
                A(f'<text x="{LAN_X+11}" y="{cy+56}" class="tiny" fill="{muted}">{_xml_escape(clip(tail, 39))}</text>')

            items = by_cam.get(g, [])
            if not items:
                empty_box(CAM_X, CAM_W, "No possible cameras" if en else "Nessuna possibile telecamera")
            for i, rec in enumerate(items):
                row = tuple(rec.get("row", ()) or ())
                cy = sy + 70 + i*(CARD_H+CARD_GAP); center = cy + CARD_H/2
                mac = str(row[0]) if len(row)>0 else rec.get("mac", "")
                vendor = str(row[1]) if len(row)>1 else ""
                score = str(row[2]) if len(row)>2 else ""
                level = str(row[3]) if len(row)>3 else ""
                prov = str(row[5]) if len(row)>5 else ""
                dashed = any(x in prov.upper() for x in ("LAN", "ROUTER", "NVR"))
                connector(anchor_x, anchor_y, bus_y, CAM_X-JOIN_GAP, CAM_X, center, dashed)
                add_card(CAM_X, cy, CAM_W, CARD_H, camera_fill, camera_border)
                A(f'<text x="{CAM_X+11}" y="{cy+21}" class="name" fill="{text}">{_xml_escape(clip(vendor or ("Possible camera" if en else "Possibile telecamera"), 27))}</text>')
                A(f'<text x="{CAM_X+11}" y="{cy+42}" class="mac" fill="{text}">{_xml_escape(mac)}</text>')
                tail = f'{prov or "-"} • {score or "-"} • {level or "-"}'
                A(f'<text x="{CAM_X+11}" y="{cy+56}" class="tiny" fill="{muted}">{_xml_escape(clip(tail, 39))}</text>')

        # Frecce topologiche SOLO nella corsia sinistra. Ogni freccia ha una label,
        # quindi non esistono piu' segmenti viola/marroni senza significato visibile.
        for i, e in enumerate(edges):
            p, c = e["parent"], e["child"]
            if p not in secpos or c not in secpos:
                continue
            yp, yc = secpos[p]["center"], secpos[c]["center"]
            lane = 48 + (i % 4) * 30
            col = cascade if e["kind"] == "cascade" else inferred
            dash = "" if e["kind"] == "cascade" else ' stroke-dasharray="7 5"'
            marker = "arrCascade" if e["kind"] == "cascade" else "arrInfer"
            A(f'<path d="M{LEFT} {yp} L{lane} {yp} L{lane} {yc} L{LEFT} {yc}" fill="none" stroke="{col}" stroke-width="3"{dash} marker-end="url(#{marker})"/>')
            mid = (yp + yc) / 2
            label = "CASCATA / AP" if e["kind"] == "cascade" else ("PROBABLE AP" if en else "AP PROBABILE")
            A(f'<rect x="{lane+5}" y="{mid-13}" width="105" height="21" rx="5" fill="#FFFFFF" stroke="{col}" stroke-width="1"/>')
            A(f'<text x="{lane+57}" y="{mid+2}" class="badge" text-anchor="middle" fill="{col}">{_xml_escape(label)}</text>')

        legend = ("Solid brown arrow = confirmed cascade/downstream AP • Dashed orange arrow = probable AP link from LAN-MAC/BSSID correlation • Dual-band radios are grouped in one AP box"
                  if en else
                  "Freccia marrone = cascata/AP confermato • Freccia arancio tratteggiata = collegamento AP probabile da correlazione MAC LAN/BSSID • Le radio dual-band sono riunite nello stesso box")
        A(f'<text x="42" y="{HEIGHT-28}" class="tiny" fill="{muted}">{_xml_escape(legend)}</text>')
        A('</svg>')

        session_stamp = str(getattr(self, "_capture_chain_session_stamp", "") or "")
        if not session_stamp:
            session_stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            self._capture_chain_session_stamp = session_stamp
        export_stamp = datetime.now().strftime("%d_%m_%y_%H_%M_%S")

        # Il grafico viene archiviato nella stessa cartella usata dal programma
        # per i file di cattura, così PCAP e topologia della sessione restano
        # raccolti nello stesso posto.
        try:
            graph_dir = Path(self.captures_dir)
        except Exception:
            graph_dir = Path(PROGRAM_DIR) / "CATTURE"
        graph_dir.mkdir(parents=True, exist_ok=True)

        out = graph_dir / ("GRAFICO_TOTALE_" + export_stamp + ".svg")

        try:
            out.write_text("\n".join(svg), encoding="utf-8")
            try:
                self.command_debug_write(f"[GRAPH] export: {out}")
            except Exception:
                pass

            popup = self._create_inapp_detail_popup(
                "SESSION NETWORK TOPOLOGY" if en else "TOPOLOGIA DI RETE DELLA SESSIONE",
                1360, 860
            )
            dark = bool(getattr(self, "night_mode", False))
            popup_bg = "#0B0F13" if dark else "#ECEFF1"
            popup_fg = "#E7EEF3" if dark else "#111111"
            body = tk.Frame(popup, bg=popup_bg)
            body.pack(fill="both", expand=True, padx=8, pady=8)
            head = tk.Frame(body, bg=popup_bg)
            head.pack(fill="x", pady=(0, 5))
            tk.Label(head, text=summary, bg=popup_bg, fg=popup_fg,
                     font=("TkDefaultFont", 10, "bold")).pack(anchor="w")
            tk.Label(head, text=str(out), bg=popup_bg, fg=popup_fg,
                     font=("TkFixedFont", 8), wraplength=1260, justify="left").pack(anchor="w", pady=(2,0))

            controls = tk.Frame(body, bg=popup_bg)
            controls.pack(fill="x", pady=(0,5))
            tk.Label(controls,
                     text=("Drag with left mouse button to move • Mouse wheel to zoom" if en else
                           "Trascina con il tasto sinistro per spostare • Rotellina per zoom"),
                     bg=popup_bg, fg=popup_fg, font=("TkDefaultFont", 9)).pack(side="left", padx=(0,14))

            canvas_wrap = tk.Frame(body, bg=popup_bg)
            canvas_wrap.pack(fill="both", expand=True)
            cv = tk.Canvas(canvas_wrap, bg=bg, highlightthickness=1, highlightbackground="#90A4AE", cursor="fleur")
            sx = tk.Scrollbar(canvas_wrap, orient="horizontal", command=cv.xview)
            syb = tk.Scrollbar(canvas_wrap, orient="vertical", command=cv.yview)
            cv.configure(xscrollcommand=sx.set, yscrollcommand=syb.set)
            cv.grid(row=0, column=0, sticky="nsew")
            syb.grid(row=0, column=1, sticky="ns")
            sx.grid(row=1, column=0, sticky="ew")
            canvas_wrap.grid_rowconfigure(0, weight=1)
            canvas_wrap.grid_columnconfigure(0, weight=1)

            _graph_text_fonts = {}
            def cbox(x, yy, w, h, fill, outline="#90A4AE", width=1, dash=None):
                kw = dict(fill=fill, outline=outline, width=width)
                if dash: kw["dash"] = dash
                return cv.create_rectangle(x, yy, x+w, yy+h, **kw)
            def ctxt(x, yy, value, size=10, bold=False, anchor="w", fill=text):
                iid = cv.create_text(x, yy, text=value, anchor=anchor, fill=fill,
                                     font=("Arial", size, "bold" if bold else "normal"))
                _graph_text_fonts[iid] = (size, bold)
                return iid
            def shadow_card(x, yy, w, h, fillc, outline, width=1):
                cbox(x+3, yy+4, w, h, panel_shadow, "", 0)
                cbox(x, yy, w, h, fillc, outline, width)
            def draw_conn(router_x, router_y, bus_y, join_x, target_x, target_y, dashed=False):
                ex = router_x + 14
                pts = (router_x, router_y, ex, router_y, ex, bus_y, join_x, bus_y, join_x, target_y, target_x, target_y)
                cv.create_line(*pts, fill=line, width=2, dash=(7,5) if dashed else None)

            ctxt(36, 28, title, 18, True)
            ctxt(36, 54, summary, 10, False, fill=muted)
            ctxt(36, 76, stamp_now, 9, False, fill=muted)

            if relation_lines:
                cbox(36, 98, 1670, relation_h-14, "#F9FBFC", "#B8C5CD", 1)
                ctxt(52, 122, "TOPOLOGY RELATIONSHIPS" if en else "RELAZIONI TOPOLOGICHE", 11, True)
                ry = 148
                for g in dual_groups:
                    radios = groups[g]["radios"]
                    desc = " ↔ ".join(f'{r.get("band") or "?"}GHz {r["bssid"].upper()}' for r in radios)
                    cv.create_line(54, ry-4, 88, ry-4, fill=dual, width=4, dash=(5,4))
                    ctxt(100, ry, clip((("SAME AP / DUAL BAND: " if en else "STESSO AP / DOPPIA BANDA: ") + group_name(g) + " — " + desc), 165), 9)
                    ry += 32
                for e in edges:
                    p, c = e["parent"], e["child"]
                    if e["kind"] == "cascade":
                        col = cascade; prefix = "CASCADE / DOWNSTREAM AP" if en else "CASCATA / AP A VALLE"; dash = None
                    else:
                        col = inferred; prefix = "PROBABLE AP LINK" if en else "COLLEGAMENTO AP PROBABILE"; dash = (7,5)
                    cv.create_line(54, ry-4, 88, ry-4, fill=col, width=4, dash=dash)
                    via = (" — LAN/WAN " + e.get("wan", "").upper()) if e.get("wan") else ""
                    sc = (f' — {e.get("score")}/100' if e["kind"] != "cascade" else "")
                    ctxt(100, ry, clip(f'{prefix}: {group_name(p)} → {group_name(c)}{via}{sc}', 165), 9)
                    ry += 32

            for idx, sec in enumerate(sections, 1):
                g, sy0, sh = sec["group"], sec["y"], sec["h"]
                gi = groups[g]
                cv.create_rectangle(LEFT+4, sy0+5, LEFT+4+SECTION_W, sy0+5+sh, fill=panel_shadow, outline="")
                cbox(LEFT, sy0, SECTION_W, sh, panel, border, 1)
                cv.create_rectangle(LEFT, sy0, LEFT+SECTION_W, sy0+44, fill=header_fill, outline="")
                cv.create_line(LEFT, sy0+44, LEFT+SECTION_W, sy0+44, fill=divider)
                role = ("MAIN ROUTER" if en else "ROUTER PRINCIPALE") if g not in incoming and g in outgoing else (("DOWNSTREAM AP / ROUTER" if en else "ACCESS POINT / ROUTER A VALLE") if g in incoming else "ROUTER / ACCESS POINT")
                ctxt(ROUTER_X, sy0+26, f'{role} {idx}', 10, True, fill=muted)
                ctxt(CLIENT_X, sy0+26, ("WI-FI CLIENTS" if en else "CLIENT WIFI") + f' ({len(by_client.get(g, []))})', 10, True, fill=muted)
                ctxt(LAN_X, sy0+26, ("LAN CANDIDATES" if en else "POSSIBILI LAN") + f' ({len(by_lan.get(g, []))})', 10, True, fill=muted)
                ctxt(CAM_X, sy0+26, ("POSSIBLE CAMERAS" if en else "POSSIBILI TELECAMERE") + f' ({len(by_cam.get(g, []))})', 10, True, fill=muted)

                router_y = sy0+68; router_h = sec["router_card_h"]
                shadow_card(ROUTER_X, router_y, ROUTER_W, router_h, router_fill, accent if gi.get("selected") else router_border, 3 if gi.get("selected") else 1)
                ctxt(ROUTER_X+12, router_y+20, clip(gi["name"], 30), 11, True)
                badges=[]
                if gi.get("captured"): badges.append("CAPTURED" if en else "CATTURATO")
                if gi.get("dual"): badges.append("DUAL BAND" if en else "DOPPIA BANDA")
                if badges: ctxt(ROUTER_X+12, router_y+40, " • ".join(badges), 8, True, fill=accent)
                yy = router_y+62
                for r in gi["radios"]:
                    band = str(r.get("band") or "?")
                    if band and "GHz" not in band: band += " GHz"
                    ctxt(ROUTER_X+12, yy, f'{band}  {r["bssid"].upper()}  CH {r.get("ch") or "-"}', 9, True)
                    yy += 24

                bus_y = sy0+54; ax=ROUTER_X+ROUTER_W; ay=router_y+router_h/2
                for x in (CLIENT_X-JOIN_GAP, LAN_X-JOIN_GAP, CAM_X-JOIN_GAP):
                    cv.create_line(x, bus_y, x, sy0+sh-24, fill=grid_line, dash=(3,6))

                def draw_empty(x,w,label):
                    cbox(x, sy0+78, w, 54, empty_fill, empty_border, 1, dash=(5,4))
                    ctxt(x+w/2, sy0+107, label, 9, anchor="center", fill=muted)

                items=by_client.get(g,[])
                if not items: draw_empty(CLIENT_X,CLIENT_W,"No Wi-Fi clients" if en else "Nessun client Wi-Fi")
                for i,rec in enumerate(items):
                    row=tuple(rec.get("row",()) or ()); cy=sy0+70+i*(CARD_H+CARD_GAP); center=cy+CARD_H/2
                    mac=str(row[0]) if len(row)>0 else rec.get("mac",""); name=str(row[1]) if len(row)>1 else ""; vendor=str(row[2]) if len(row)>2 else ""; pwr=str(row[3]) if len(row)>3 else ""
                    name=name or vendor or ("Wi-Fi client" if en else "Client Wi-Fi")
                    draw_conn(ax,ay,bus_y,CLIENT_X-JOIN_GAP,CLIENT_X,center,False); shadow_card(CLIENT_X,cy,CLIENT_W,CARD_H,client_fill,client_border)
                    ctxt(CLIENT_X+10,cy+19,clip(name,27),10,True); ctxt(CLIENT_X+10,cy+40,mac,9,True)
                    tail=vendor if vendor and vendor!=name else ""; tail += ((" • " if tail else "")+"PWR "+pwr) if pwr else ""
                    ctxt(CLIENT_X+10,cy+54,clip(tail,39),8,fill=muted)

                items=by_lan.get(g,[])
                if not items: draw_empty(LAN_X,LAN_W,"No LAN candidates" if en else "Nessun candidato LAN")
                for i,rec in enumerate(items):
                    row=tuple(rec.get("row",()) or ()); cy=sy0+70+i*(CARD_H+CARD_GAP); center=cy+CARD_H/2
                    vendor=str(row[0]) if len(row)>0 else ""; role2=str(row[1]) if len(row)>1 else ""; level=str(row[2]) if len(row)>2 else ""; mac=str(row[4]) if len(row)>4 else rec.get("mac","")
                    name=role2 or vendor or ("LAN candidate" if en else "Candidato LAN")
                    draw_conn(ax,ay,bus_y,LAN_X-JOIN_GAP,LAN_X,center,True); shadow_card(LAN_X,cy,LAN_W,CARD_H,lan_fill,lan_border)
                    ctxt(LAN_X+10,cy+19,clip(name,27),10,True); ctxt(LAN_X+10,cy+40,mac,9,True); ctxt(LAN_X+10,cy+54,clip(vendor+((" • "+level) if level else ""),39),8,fill=muted)

                items=by_cam.get(g,[])
                if not items: draw_empty(CAM_X,CAM_W,"No possible cameras" if en else "Nessuna possibile telecamera")
                for i,rec in enumerate(items):
                    row=tuple(rec.get("row",()) or ()); cy=sy0+70+i*(CARD_H+CARD_GAP); center=cy+CARD_H/2
                    mac=str(row[0]) if len(row)>0 else rec.get("mac",""); vendor=str(row[1]) if len(row)>1 else ""; score=str(row[2]) if len(row)>2 else ""; level=str(row[3]) if len(row)>3 else ""; prov=str(row[5]) if len(row)>5 else ""
                    dashed=any(x in prov.upper() for x in ("LAN","ROUTER","NVR"))
                    draw_conn(ax,ay,bus_y,CAM_X-JOIN_GAP,CAM_X,center,dashed); shadow_card(CAM_X,cy,CAM_W,CARD_H,camera_fill,camera_border)
                    ctxt(CAM_X+10,cy+19,clip(vendor or ("Possible camera" if en else "Possibile telecamera"),27),10,True); ctxt(CAM_X+10,cy+40,mac,9,True); ctxt(CAM_X+10,cy+54,clip(f'{prov or "-"} • {score or "-"} • {level or "-"}',39),8,fill=muted)

            for i,e in enumerate(edges):
                p,c=e["parent"],e["child"]
                if p not in secpos or c not in secpos: continue
                yp,yc=secpos[p]["center"],secpos[c]["center"]; lane=48+(i%4)*30
                col=cascade if e["kind"]=="cascade" else inferred; dash=None if e["kind"]=="cascade" else (7,5)
                cv.create_line(LEFT,yp,lane,yp,lane,yc,LEFT,yc,fill=col,width=3,dash=dash,arrow=tk.LAST)
                mid=(yp+yc)/2; lbl="CASCATA / AP" if e["kind"]=="cascade" else ("PROBABLE AP" if en else "AP PROBABILE")
                cbox(lane+5,mid-13,108,22,label_bg,col,1); ctxt(lane+59,mid-2,lbl,8,True,anchor="center",fill=col)

            ctxt(36,HEIGHT-24,legend,8,fill=muted)

            _zoom={"value":1.0}
            zoom_label=tk.Label(controls,text="100%",bg=popup_bg,fg=popup_fg,font=("TkDefaultFont",9,"bold"))
            def refresh_region():
                try:
                    bbox=cv.bbox("all")
                    if bbox: cv.configure(scrollregion=(bbox[0]-50,bbox[1]-50,bbox[2]+50,bbox[3]+50))
                except Exception: pass
            def apply_zoom(factor,event=None):
                old=float(_zoom["value"]); new=max(0.40,min(3.50,old*float(factor))); factor=new/old
                if abs(factor-1.0)<0.001: return
                try:
                    if event is not None: cx,cy=cv.canvasx(event.x),cv.canvasy(event.y)
                    else: cx,cy=cv.canvasx(max(1,cv.winfo_width())/2),cv.canvasy(max(1,cv.winfo_height())/2)
                    cv.scale("all",cx,cy,factor,factor); _zoom["value"]=new
                    for iid,(base,bold) in list(_graph_text_fonts.items()):
                        try: cv.itemconfigure(iid,font=("Arial",max(6,int(round(base*new))),"bold" if bold else "normal"))
                        except Exception: pass
                    zoom_label.configure(text=f'{int(round(new*100))}%'); refresh_region()
                except Exception: pass
            def zoom_reset():
                cur=float(_zoom["value"])
                if cur>0: apply_zoom(1.0/cur)
                try: cv.xview_moveto(0); cv.yview_moveto(0)
                except Exception: pass
            def graph_ctrl_button(label, command, width=None):
                kw = dict(
                    text=label, command=command, cursor="hand2",
                    bg=("#182129" if dark else "#E7E7E7"),
                    fg=("#E7EEF3" if dark else "#111111"),
                    activebackground=("#2A3945" if dark else "#F4F4F4"),
                    activeforeground=("#FFFFFF" if dark else "#111111"),
                    relief="flat" if dark else "raised"
                )
                if width is not None:
                    kw["width"] = width
                return tk.Button(controls, **kw)
            graph_ctrl_button("−", lambda:apply_zoom(1/1.20), 3).pack(side="right",padx=3)
            zoom_label.pack(side="right",padx=3)
            graph_ctrl_button("+", lambda:apply_zoom(1.20), 3).pack(side="right",padx=3)
            graph_ctrl_button(("RESET ZOOM" if en else "ZOOM 100%"), zoom_reset).pack(side="right",padx=(3,10))

            def pan_start(event):
                try: cv.scan_mark(event.x,event.y); cv.configure(cursor="hand2")
                except Exception: pass
            def pan_move(event):
                try: cv.scan_dragto(event.x,event.y,gain=1)
                except Exception: pass
            def pan_end(event):
                try: cv.configure(cursor="fleur")
                except Exception: pass
            def wheel(event):
                try:
                    if getattr(event,"num",None)==4: factor=1.12
                    elif getattr(event,"num",None)==5: factor=1/1.12
                    else: factor=1.12 if event.delta>0 else 1/1.12
                    apply_zoom(factor,event); return "break"
                except Exception: return None
            cv.bind("<ButtonPress-1>",pan_start); cv.bind("<B1-Motion>",pan_move); cv.bind("<ButtonRelease-1>",pan_end)
            cv.bind("<MouseWheel>",wheel); cv.bind("<Button-4>",wheel); cv.bind("<Button-5>",wheel)
            refresh_region()
            self._show_inapp_detail_popup(popup)
            try:
                self.set_status((f"Network graph updated: {out.name}" if en else f"Grafico di rete aggiornato: {out.name}"))
            except Exception: pass
        except Exception as e:
            try:
                messagebox.showerror("EXPORT GRAPH" if en else "ESPORTA GRAFICO",
                                     (f"Unable to create the network graph:\n{e}" if en else f"Impossibile creare il grafico di rete:\n{e}"))
            except Exception:
                pass

    def open_command_debug(self):
        """Apre DEBUG come pannello interno alla GUI, senza creare finestre del sistema."""
        # Se è già aperto, portalo semplicemente in primo piano.
        try:
            if self.command_debug_window is not None and self.command_debug_window.winfo_exists():
                self.command_debug_window.lift()
                try:
                    self.command_debug_window.focus_set()
                except Exception:
                    pass
                return
        except Exception:
            self.command_debug_window = None
            self.command_debug_text = None

        is_en = getattr(self, "language", "it") == "en"
        title = "COMMAND DEBUG" if is_en else "DEBUG COMANDI"

        # Riusa il sistema di popup interno già adottato per LAN/telecamere.
        popup = self._create_inapp_detail_popup(title, 980, 640)
        self.command_debug_window = popup
        try:
            if bool(getattr(self, "night_mode", False)):
                popup.configure(
                    bg="#12171B",
                    highlightbackground="#232C31",
                    highlightcolor="#232C31",
                    highlightthickness=1,
                    bd=0,
                    relief="flat"
                )
        except Exception:
            pass

        dark = bool(getattr(self, "night_mode", False))
        bg = "#12171B" if dark else "#ECEFF1"
        panel = "#1A2126" if dark else "#FFFFFF"
        title_bg = "#20272B" if dark else "#B0BEC5"

        # DEBUG: applica il colore corretto PRIMA che il pannello venga mostrato.
        # Questo elimina superfici bianche e flash in modalità notte.
        try:
            popup.configure(bg=bg)
            for child in popup.winfo_children():
                try:
                    if isinstance(child, (tk.Frame, tk.Label)):
                        child.configure(bg=title_bg if child.winfo_y() <= 45 else bg)
                except Exception:
                    pass
        except Exception:
            pass
        fg = "#E7ECEF" if dark else "#111111"
        muted = "#AAB3BA" if dark else "#555555"
        select_bg = "#2B4558" if dark else "#C9DDF4"
        select_fg = "#FFFFFF" if dark else "#111111"

        # Area contenuto sotto la titlebar già creata da _create_inapp_detail_popup.
        body = tk.Frame(popup, bg=bg, bd=0, highlightthickness=0)
        body.pack(fill="both", expand=True, padx=10, pady=(8,10))
        body.columnconfigure(0, weight=1)
        body.rowconfigure(1, weight=1)

        header = tk.Label(
            body,
            text=("Executed commands and diagnostic output" if is_en
                  else "Comandi eseguiti e output diagnostico"),
            bg=bg,
            fg=fg,
            font=("TkDefaultFont", 10, "bold"),
            anchor="w"
        )
        header.grid(row=0, column=0, sticky="ew", pady=(0,6))

        text_frame = tk.Frame(body, bg=bg, bd=0, highlightthickness=0)
        text_frame.grid(row=1, column=0, sticky="nsew")
        text_frame.columnconfigure(0, weight=1)
        text_frame.rowconfigure(0, weight=1)

        dbg = tk.Text(
            text_frame,
            wrap="none",
            font=("TkFixedFont", 10),
            bg=panel,
            fg=fg,
            insertbackground=fg,
            selectbackground=select_bg,
            selectforeground=select_fg,
            borderwidth=0,
            highlightthickness=1,
            highlightbackground=("#232C31" if dark else "#B0BEC5"),
            highlightcolor=("#232C31" if dark else "#90A4AE")
        )
        dbg.grid(row=0, column=0, sticky="nsew")
        self.command_debug_text = dbg

        ybar = ttk.Scrollbar(text_frame, orient="vertical", command=dbg.yview)
        ybar.grid(row=0, column=1, sticky="ns")
        xbar = ttk.Scrollbar(text_frame, orient="horizontal", command=dbg.xview)
        xbar.grid(row=1, column=0, sticky="ew")
        dbg.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)

        # DEBUG copiabile: Ctrl+C, Ctrl+A e menu col tasto destro.
        def _debug_copy(_event=None):
            try:
                txt = dbg.get("sel.first", "sel.last")
                self.root.clipboard_clear()
                self.root.clipboard_append(txt)
                self.root.update_idletasks()
            except Exception:
                pass
            return "break"

        def _debug_select_all(_event=None):
            try:
                dbg.tag_add("sel", "1.0", "end-1c")
                dbg.mark_set("insert", "1.0")
                dbg.see("1.0")
                dbg.focus_set()
            except Exception:
                pass
            return "break"

        dbg.bind("<Control-c>", _debug_copy, add="+")
        dbg.bind("<Control-C>", _debug_copy, add="+")
        dbg.bind("<Control-a>", _debug_select_all, add="+")
        dbg.bind("<Control-A>", _debug_select_all, add="+")

        debug_menu = tk.Menu(dbg, tearoff=0)
        debug_menu.add_command(
            label=("Copy" if is_en else "Copia"),
            command=_debug_copy
        )
        debug_menu.add_command(
            label=("Select all" if is_en else "Seleziona tutto"),
            command=_debug_select_all
        )

        def _debug_context_menu(event):
            try:
                dbg.focus_set()
                debug_menu.tk_popup(event.x_root, event.y_root)
            finally:
                try:
                    debug_menu.grab_release()
                except Exception:
                    pass
            return "break"

        dbg.bind("<Button-3>", _debug_context_menu, add="+")
        # Compatibilità con sistemi dove il menu contestuale usa Button-2.
        dbg.bind("<Button-2>", _debug_context_menu, add="+")

        controls = tk.Frame(body, bg=bg, bd=0, highlightthickness=0)
        controls.grid(row=2, column=0, sticky="ew", pady=(8,0))

        def clear_debug():
            try:
                dbg.configure(state="normal")
                dbg.delete("1.0", "end")
            except Exception:
                pass

        clear_btn = tk.Button(
            controls,
            text=("CLEAR" if is_en else "PULISCI"),
            command=clear_debug,
            padx=14,
            pady=4,
            bg=("#2B3940" if dark else "#455A64"),
            fg="white",
            activebackground=("#3C4F59" if dark else "#607D8B"),
            activeforeground="white",
            relief="flat",
            cursor="hand2"
        )
        clear_btn.pack(side="left")

        close_btn = tk.Button(
            controls,
            text=("CLOSE" if is_en else "CHIUDI"),
            command=popup._close_popup,
            padx=14,
            pady=4,
            bg=("#2B3940" if dark else "#455A64"),
            fg="white",
            activebackground=("#3C4F59" if dark else "#607D8B"),
            activeforeground="white",
            relief="flat",
            cursor="hand2"
        )
        close_btn.pack(side="right")

        # Se esiste un buffer precedente, mostrane il contenuto.
        try:
            existing = getattr(self, "_command_debug_buffer", None)
            if existing:
                dbg.insert("end", "".join(existing))
                dbg.see("end")
        except Exception:
            pass

        # Quando il pannello viene distrutto, azzera i riferimenti.
        def on_destroy(_event=None):
            try:
                if self.command_debug_window is popup:
                    self.command_debug_window = None
                    self.command_debug_text = None
            except Exception:
                pass

        popup.bind("<Destroy>", on_destroy, add="+")
        popup.bind("<Escape>", lambda _e: popup._close_popup())

        # DEBUG ridimensionabile con il mouse: trascina l'angolo in basso a destra.
        # Il pannello rimane sempre dentro i limiti della finestra principale.
        resize_grip = tk.Label(
            popup,
            text="◢",
            font=("TkDefaultFont", 12, "bold"),
            bg=("#20272B" if dark else "#B0BEC5"),
            fg=("#5B666C" if dark else "#546E7A"),
            bd=0,
            padx=2,
            pady=0,
            cursor="sizing"
        )
        resize_grip.place(relx=1.0, rely=1.0, x=-2, y=-2, anchor="se")

        popup._resize_start_x = 0
        popup._resize_start_y = 0
        popup._resize_start_w = 0
        popup._resize_start_h = 0

        def _debug_resize_start(event):
            try:
                popup._resize_start_x = int(event.x_root)
                popup._resize_start_y = int(event.y_root)
                popup._resize_start_w = int(popup.winfo_width())
                popup._resize_start_h = int(popup.winfo_height())
                popup.lift()
            except Exception:
                pass

        def _debug_resize_move(event):
            try:
                dx = int(event.x_root) - int(popup._resize_start_x)
                dy = int(event.y_root) - int(popup._resize_start_y)

                rw = max(1, int(self.root.winfo_width()))
                rh = max(1, int(self.root.winfo_height()))
                px = max(0, int(popup.winfo_x()))
                py = max(0, int(popup.winfo_y()))

                min_w = 520
                min_h = 340
                max_w = max(min_w, rw - px)
                max_h = max(min_h, rh - py)

                nw = max(min_w, min(max_w, popup._resize_start_w + dx))
                nh = max(min_h, min(max_h, popup._resize_start_h + dy))

                popup.place_configure(width=nw, height=nh)
                popup._popup_width = nw
                popup._popup_height = nh
                popup.lift()
                resize_grip.lift()
            except Exception:
                pass

        resize_grip.bind("<ButtonPress-1>", _debug_resize_start)
        resize_grip.bind("<B1-Motion>", _debug_resize_move)

        # DEBUG: trascinamento semplice puntando dentro la finestra e muovendo
        # il mouse con il tasto sinistro premuto. Non è più necessario afferrare
        # soltanto la barra superiore.
        popup._free_drag_start_x = 0
        popup._free_drag_start_y = 0
        popup._free_drag_orig_x = 0
        popup._free_drag_orig_y = 0

        def _debug_free_drag_start(event):
            try:
                # Non iniziare il trascinamento se si sta usando un pulsante,
                # una scrollbar o il grip di ridimensionamento.
                w = event.widget
                cls = str(w.winfo_class())
                if isinstance(w, tk.Button) or w is resize_grip or cls in ("TScrollbar", "Scrollbar"):
                    return

                popup._free_drag_start_x = int(event.x_root)
                popup._free_drag_start_y = int(event.y_root)
                info = popup.place_info()
                popup._free_drag_orig_x = int(float(info.get("x", popup.winfo_x())))
                popup._free_drag_orig_y = int(float(info.get("y", popup.winfo_y())))
                popup._free_drag_enabled = True
                popup.lift()
            except Exception:
                popup._free_drag_enabled = False

        def _debug_free_drag_move(event):
            try:
                if not bool(getattr(popup, "_free_drag_enabled", False)):
                    return

                dx = int(event.x_root) - int(popup._free_drag_start_x)
                dy = int(event.y_root) - int(popup._free_drag_start_y)

                rw = max(1, int(self.root.winfo_width()))
                rh = max(1, int(self.root.winfo_height()))
                pw = max(1, int(popup.winfo_width()))
                ph = max(1, int(popup.winfo_height()))

                nx = popup._free_drag_orig_x + dx
                ny = popup._free_drag_orig_y + dy
                nx = max(0, min(nx, max(0, rw - pw)))
                ny = max(0, min(ny, max(0, rh - ph)))

                popup.place_configure(x=nx, y=ny)
                popup.lift()
                resize_grip.lift()
            except Exception:
                pass

        def _debug_free_drag_end(_event=None):
            popup._free_drag_enabled = False

        def _bind_debug_drag(widget):
            try:
                # Evita di sovrascrivere il grip e i pulsanti.
                cls = str(widget.winfo_class())
                # NON intercettare il mouse nel Text DEBUG:
                # deve poter selezionare/copiarne liberamente il contenuto.
                if (
                    not isinstance(widget, (tk.Button, tk.Text))
                    and widget is not resize_grip
                    and cls not in ("TScrollbar", "Scrollbar", "Text")
                ):
                    widget.bind("<ButtonPress-1>", _debug_free_drag_start, add="+")
                    widget.bind("<B1-Motion>", _debug_free_drag_move, add="+")
                    widget.bind("<ButtonRelease-1>", _debug_free_drag_end, add="+")
                for child in widget.winfo_children():
                    _bind_debug_drag(child)
            except Exception:
                pass

        _bind_debug_drag(popup)

        # Tema DEBUG completo PRIMA della visualizzazione.
        # In modalità notte nessun Frame/Label/Button interno deve mantenere il bianco.
        if dark:
            def _darken_debug_widget(widget):
                try:
                    cls = widget.winfo_class()
                    if cls in ("Frame", "Labelframe"):
                        widget.configure(bg=bg)
                    elif cls == "Label":
                        widget.configure(bg=bg, fg=fg)
                    elif cls == "Button":
                        widget.configure(
                            bg="#2B3940", fg="#E7ECEF",
                            activebackground="#3C4F59",
                            activeforeground="#FFFFFF"
                        )
                except Exception:
                    pass
                try:
                    for child in widget.winfo_children():
                        _darken_debug_widget(child)
                except Exception:
                    pass
            _darken_debug_widget(popup)

            # Ripristina specificamente la barra titolo più scura.
            try:
                titlebar = popup.winfo_children()[0]
                titlebar.configure(bg=title_bg)
                for child in titlebar.winfo_children():
                    try:
                        child.configure(bg=title_bg, fg=fg)
                    except Exception:
                        pass
            except Exception:
                pass

        try:
            popup.update_idletasks()
        except Exception:
            pass

        self._apply_debug_panel_theme()
        self._show_inapp_detail_popup(popup)
        self._apply_debug_panel_theme()
        try:
            resize_grip.configure(
                bg=("#20272B" if dark else "#B0BEC5"),
                fg=("#5B666C" if dark else "#546E7A")
            )
            resize_grip.lift()
        except Exception:
            pass

        # DEBUG NON MODALE:
        # resta visibile e trascinabile, ma non blocca i controlli della GUI sotto.
        try:
            popup.grab_release()
        except Exception:
            pass
        try:
            self.root.focus_set()
        except Exception:
            pass


    def command_debug_write(self, source, command=None):
        """Registra i comandi nel buffer DEBUG e nel pannello interno, se aperto."""
        if not getattr(self, "command_debug_enabled", True):
            return
        try:
            if command is None:
                message = str(source)
            else:
                message = f"[{source}] {command}"
            if not message.endswith("\n"):
                message += "\n"

            if not isinstance(getattr(self, "_command_debug_buffer", None), list):
                self._command_debug_buffer = []
            self._command_debug_buffer.append(message)

            # Limita il buffer per evitare crescita indefinita.
            if len(self._command_debug_buffer) > 3000:
                self._command_debug_buffer = self._command_debug_buffer[-2000:]

            widget = getattr(self, "command_debug_text", None)
            if widget is not None and widget.winfo_exists():
                widget.configure(state="normal")
                widget.insert("end", message)
                widget.see("end")
        except Exception:
            pass


    def logmsg(self, msg):
        def _w():
            self.log.insert("end", msg.rstrip()+"\n")
            self.log.see("end")
        self.root.after(0, _w)

    def set_status(self, s):
        self.root.after(0, self.status.set, s)

    def _enforce_scan_progress_blue(self):
        """Mantiene ROUTER e CLIENT sempre blu, anche quando cambia tema o comando."""
        trough = "#262a31" if getattr(self, "night_mode", False) else "#d9d9d9"
        border = "#262a31" if getattr(self, "night_mode", False) else "#b8b8b8"
        try:
            self.style.configure(
                "ScanBlue.Horizontal.TProgressbar",
                thickness=16,
                troughcolor=trough,
                background=("#168CFF" if getattr(self, "night_mode", False) else "#1565C0"),
                bordercolor=border,
                lightcolor=("#1687E8" if getattr(self, "night_mode", False) else "#1565C0"),
                darkcolor=("#084A88" if getattr(self, "night_mode", False) else "#1565C0")
            )
        except Exception:
            pass

    def _set_work_progress_color(self, mode):
        """
        Imposta il colore della barra BLOCCO/CATTURA.
        - blue: CATTURA PASSIVA
        - red: DISTURBO / BLOCCO ROUTER / BLOCCO CLIENT
        """
        mode = "red" if str(mode).lower() == "red" else "blue"
        self.work_progress_color = mode

        night = bool(getattr(self, "night_mode", False))
        if mode == "red":
            bar = "#741A1A" if night else "#FF0000"
        else:
            bar = "#0B5FAE" if night else "#1565C0"

        trough = "#262a31" if getattr(self, "night_mode", False) else "#e1e1e1"
        border = "#262a31" if getattr(self, "night_mode", False) else "#b8b8b8"

        try:
            self.style.configure(
                "Work.Horizontal.TProgressbar",
                background=bar,
                lightcolor=bar,
                darkcolor=bar,
                troughcolor=trough,
                bordercolor=border,
                thickness=16
            )
        except Exception:
            pass

        # Il colore della barra lavoro non deve mai influenzare ROUTER/CLIENT.
        self._enforce_scan_progress_blue()

    def set_progress(self, percent, text=None, phase=None, detail=None):
        """
        Aggiorna la barra cattura con valore frazionario reale.
        La percentuale testuale resta intera, ma la barra si muove in modo fluido.
        """
        percent = max(0.0, min(100.0, float(percent)))
        def _u():
            self.progress_value.set(percent)
            display = text if text is not None else f"{percent:.0f}%"
            self.progress_text.set(display)
            self.progress_caption.set(f"AVANZAMENTO CATTURA: {percent:.0f}%")
            self.capture_completed_pct.set(f"{percent:.0f}%")
            # NON arrotondare il valore grafico: mantiene i decimali.
            self.capture_progress_value.set(percent)
            if phase is not None:
                self.phase.set(phase)
            if detail is not None:
                self.work_detail.set(detail)
        self.root.after(0, _u)

    def check_deps(self):
        missing=[x for x in ("iw","airodump-ng","tshark") if shutil.which(x) is None]
        if missing:
            messagebox.showerror("Dipendenze mancanti","Mancano: "+", ".join(missing))
            return False
        if os.geteuid()!=0:
            messagebox.showerror("Permessi","Avvia il programma tramite il launcher con sudo.")
            return False
        return True

    def get_interfaces(self):
        """Rileva le interfacce Wi-Fi senza dipendere da una sola sorgente.

        `iw dev` resta la fonte principale per tipo managed/monitor, ma alcune
        schede/driver USB possono comparire in /sys/class/net durante una fase
        transitoria anche quando `iw dev` restituisce output incompleto.
        """
        names = []
        types = {}

        def add_iface(name, iface_type=""):
            name = str(name or "").strip()
            if not name or name == "lo":
                return
            if name not in names:
                names.append(name)
            if iface_type or name not in types:
                types[name] = iface_type or types.get(name, "")

        # 1) Fonte primaria: nl80211/iw.
        try:
            p = run(["iw", "dev"], timeout=6)
            cur = None
            if p.returncode == 0:
                for line in (p.stdout or "").splitlines():
                    line_s = line.strip()
                    if line_s.startswith("Interface "):
                        cur = line_s.split(None, 1)[1].strip()
                        add_iface(cur)
                    elif cur and line_s.startswith("type "):
                        types[cur] = line_s.split(None, 1)[1].strip()
        except Exception:
            pass

        # 2) Fallback kernel/sysfs: recupera WLAN reali anche se l'output di
        # `iw dev` è temporaneamente vuoto/incompleto.
        try:
            net_root = Path("/sys/class/net")
            for dev in net_root.iterdir():
                name = dev.name
                if name == "lo":
                    continue

                wireless = (dev / "wireless").exists()
                phy80211 = (dev / "phy80211").exists()
                name_wifi = bool(re.match(r"^(?:wlan|wl)[A-Za-z0-9_.-]*$", name, re.I))

                if wireless or phy80211 or name_wifi:
                    add_iface(name)

                    # Se iw non aveva fornito il tipo, interrogazione puntuale.
                    if not types.get(name):
                        try:
                            info = run(["iw", "dev", name, "info"], timeout=4)
                            m = re.search(
                                r"(?mi)^\\s*type\\s+(\\S+)\\s*$",
                                (info.stdout or "") + "\\n" + (info.stderr or "")
                            )
                            if m:
                                types[name] = m.group(1).strip()
                        except Exception:
                            pass
        except Exception:
            pass

        # 3) Ultimo fallback: /proc/net/wireless. Utile con alcuni driver legacy.
        try:
            proc_wireless = Path("/proc/net/wireless")
            if proc_wireless.exists():
                for line in proc_wireless.read_text(errors="ignore").splitlines()[2:]:
                    if ":" not in line:
                        continue
                    add_iface(line.split(":", 1)[0].strip())
        except Exception:
            pass

        # Ordine naturale: wlan0, wlan1, wlan2... prima degli altri nomi wl*.
        def natural_key(name):
            m = re.match(r"^(wlan)(\\d+)$", name, re.I)
            if m:
                return (0, int(m.group(2)))
            return (1, name.lower())

        names.sort(key=natural_key)
        for name in names:
            types.setdefault(name, "")
        return names, types

    def is_usb_network_interface(self, iface):
        """Restituisce True se l'interfaccia di rete appartiene a un dispositivo USB."""
        iface=(iface or "").strip()
        if not iface:
            return False
        try:
            dev=Path("/sys/class/net") / iface / "device"
            if not dev.exists():
                return False
            real=str(dev.resolve()).lower()
            return "/usb" in real
        except Exception:
            return False

    def interface_origin_text(self, iface):
        """Mostra solo ':' seguito dal tipo di interfaccia, senza la parola ORIGINE."""
        iface=(iface or "").strip()
        if not iface:
            return ": --"
        if self.is_usb_network_interface(iface):
            return ": USB / ESTERNA"
        return ": PC / INTERNA"

    def _update_iface_origin(self):
        self.iface_origin.set(self.interface_origin_text(self.iface.get()))
        try:
            dark = bool(getattr(self, "night_mode", False))
            self.iface_origin_label.configure(
                bg=("#111111" if dark else self.root.cget("bg")),
                fg=("#E6E6E6" if dark else "#000000")
            )
        except Exception:
            pass

    def _refresh_iface_status_theme(self):
        """Aggiorna visibilità origine e riquadro MONITOR MODE dopo cambio tema."""
        try:
            dark = bool(getattr(self, "night_mode", False))
            self.iface_origin_label.configure(
                bg=("#111111" if dark else self.root.cget("bg")),
                fg=("#E6E6E6" if dark else "#000000")
            )
        except Exception:
            pass

        try:
            monitor_on = str(self.monitor_mode_state.get()).strip().upper().endswith("ON")
            border_color = "#FFFFFF" if dark else "#000000"
            self.monitor_mode_label.configure(
                bg=("#2E7D32" if monitor_on else "#FF0000"),
                fg="#FFFFFF",
                highlightbackground=border_color,
                highlightcolor=border_color
            )
        except Exception:
            pass

    def _on_iface_selected(self, _event=None):
        self._update_iface_origin()

    def _any_protected_operation_active(self):
        """True se una delle attività che usa la Wi-Fi è ancora in corso."""
        try:
            if not getattr(self, "ap_scan_finished", True):
                return True
        except Exception:
            pass
        try:
            if not getattr(self, "client_scan_finished", True):
                return True
        except Exception:
            pass
        try:
            if bool(getattr(self, "diegi_running", False)):
                return True
        except Exception:
            pass

        for attr in (
            "capture_process",
            "aireplay_ng_router_process",
            "aireplay_ng_client_process",
        ):
            try:
                proc = getattr(self, attr, None)
                if proc is not None and proc.poll() is None:
                    return True
            except Exception:
                pass

        return bool(getattr(self, "_suspend_inhibit_reasons", set()))

    def _acquire_suspend_inhibitor(self, reason="wifi-operation"):
        """
        Impedisce sleep/idle mentre una cattura o scansione è attiva.
        Usa systemd-inhibit quando disponibile; se non è disponibile il
        programma continua normalmente e resta attivo il recovery post-resume.
        """
        try:
            self._suspend_inhibit_reasons.add(str(reason))
        except Exception:
            self._suspend_inhibit_reasons = {str(reason)}

        proc = getattr(self, "_suspend_inhibit_process", None)
        try:
            if proc is not None and proc.poll() is None:
                return
        except Exception:
            pass

        inhibitor = shutil.which("systemd-inhibit")
        if not inhibitor:
            self.logmsg("systemd-inhibit non disponibile: attivo solo ripristino post-standby.")
            return

        cmd = [
            inhibitor,
            "--what=sleep:idle",
            "--who=WiFi Audit GUI",
            "--why=Wireless capture/scanning active",
            "--mode=block",
            "sleep", "infinity",
        ]
        try:
            self._suspend_inhibit_process = subprocess.Popen(
                cmd,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
            )
            self.logmsg("Protezione standby attivata durante attività Wi-Fi.")
        except Exception as e:
            self._suspend_inhibit_process = None
            self.logmsg(f"Protezione standby non disponibile: {e}")

    def _release_suspend_inhibitor(self, reason=None, force=False):
        """Rilascia l'inibitore quando non restano attività protette."""
        if reason is not None:
            try:
                self._suspend_inhibit_reasons.discard(str(reason))
            except Exception:
                pass

        if not force:
            try:
                if self._suspend_inhibit_reasons:
                    return
            except Exception:
                pass

            # Lascia qualche istante ai worker per aggiornare i relativi flag/processi.
            active = False
            try:
                if not getattr(self, "ap_scan_finished", True):
                    active = True
                if not getattr(self, "client_scan_finished", True):
                    active = True
                if bool(getattr(self, "diegi_running", False)):
                    active = True
            except Exception:
                pass
            if active:
                return

        proc = getattr(self, "_suspend_inhibit_process", None)
        self._suspend_inhibit_process = None
        if proc is not None:
            try:
                if proc.poll() is None:
                    proc.terminate()
                    try:
                        proc.wait(timeout=1)
                    except Exception:
                        proc.kill()
            except Exception:
                pass

        if force:
            try:
                self._suspend_inhibit_reasons.clear()
            except Exception:
                pass

    def _release_suspend_inhibitor_later(self, reason=None):
        try:
            self.root.after(
                700,
                lambda r=reason: self._release_suspend_inhibitor(r)
            )
        except Exception:
            self._release_suspend_inhibitor(reason)

    def _iface_is_monitor_now(self, iface):
        iface = (iface or "").strip()
        if not iface:
            return False
        try:
            p = run(["iw", "dev", iface, "info"], timeout=5)
            if p.returncode != 0:
                return False
            return bool(re.search(r"(?mi)^\s*type\s+monitor\s*$", p.stdout or ""))
        except Exception:
            return False

    def _recover_after_resume(self):
        """Rileva nuovamente WLAN e monitor mode dopo un resume reale."""
        preferred = (
            getattr(self, "_resume_preferred_iface", "")
            or getattr(self, "active_monitor_iface", "")
            or (self.iface.get() or "").strip()
        )
        wanted_monitor = bool(getattr(self, "_resume_monitor_was_active", False))

        try:
            msg = (
                "Recovering Wi-Fi interface after standby..."
                if getattr(self, "language", "it") == "en"
                else "Ripristino interfaccia Wi-Fi dopo standby..."
            )
            self.set_status(msg)
        except Exception:
            pass

        try:
            self.refresh_interfaces(preferred=preferred)
        except Exception as e:
            self.logmsg(f"Refresh interfacce dopo resume: {e}")

        # Processi esterni possono essere terminati dal suspend/driver.
        try:
            proc = getattr(self, "ap_scan_process", None)
            if proc is not None and proc.poll() is not None:
                self.ap_scan_process = None
                self.ap_scan_finished = True
                self._stop_button_blink("scan_wifi_button")
                self._release_suspend_inhibitor_later("ap-scan")
        except Exception:
            pass
        try:
            proc = getattr(self, "client_scan_process", None)
            if proc is not None and proc.poll() is not None:
                self.client_scan_process = None
                self.client_scan_finished = True
                self._stop_button_blink("scan_client_button")
                self._release_suspend_inhibitor_later("client-scan")
        except Exception:
            pass
        try:
            proc = getattr(self, "capture_process", None)
            if proc is not None and proc.poll() is not None:
                self.capture_process = None
                self._stop_button_blink("start_capture_button")
                self._release_suspend_inhibitor_later("capture")
        except Exception:
            pass

        current = (self.iface.get() or preferred or "").strip()
        if current:
            try:
                self.iface.set(current)
            except Exception:
                pass

        if current and self._iface_is_monitor_now(current):
            self._set_monitor_mode_visible_state(current, True)
            try:
                self.set_status(
                    f"Wi-Fi interface restored after standby: {current}"
                    if getattr(self, "language", "it") == "en"
                    else f"Interfaccia Wi-Fi ripristinata dopo standby: {current}"
                )
            except Exception:
                pass
            return

        self._set_monitor_mode_visible_state(current, False)

        # Se prima dello standby era realmente in monitor mode, prova a ripristinarlo.
        if wanted_monitor and current:
            # Recovery SOLO dopo un resume rilevato. Nessun watchdog periodico
            # modifica la scheda durante una normale scansione.
            try:
                self.logmsg(f"Resume: verifica monitor mode su {current}.")
                if not self._iface_is_monitor_now(current):
                    self.root.after(900, self.enable_monitor_mode)
            except Exception:
                pass

    def _start_resume_watchdog(self):
        """
        Confronta CLOCK_REALTIME e monotonic. In Linux monotonic non avanza
        durante suspend: un forte scarto tra i due delta indica un resume.
        """
        try:
            if self._resume_watch_after is not None:
                return
        except Exception:
            pass

        self._resume_last_wall = time.time()
        self._resume_last_mono = time.monotonic()

        def tick():
            try:
                now_wall = time.time()
                now_mono = time.monotonic()

                wall_delta = max(0.0, now_wall - self._resume_last_wall)
                mono_delta = max(0.0, now_mono - self._resume_last_mono)
                suspend_gap = wall_delta - mono_delta

                # Memorizza lo stato desiderato per un eventuale resume successivo.
                try:
                    chosen = (self.active_monitor_iface or self.iface.get() or "").strip()
                    if chosen:
                        self._resume_preferred_iface = chosen
                    self._resume_monitor_was_active = bool(
                        self.active_monitor_iface
                        or str(self.monitor_mode_state.get()).strip().upper().endswith("ON")
                    )
                except Exception:
                    pass

                self._resume_last_wall = now_wall
                self._resume_last_mono = now_mono

                if suspend_gap >= 4.0:
                    self.logmsg(f"Possibile resume rilevato: gap={suspend_gap:.1f}s")
                    self.root.after(1800, self._recover_after_resume)

                self._resume_watch_after = self.root.after(2000, tick)
            except Exception:
                try:
                    self._resume_watch_after = self.root.after(3000, tick)
                except Exception:
                    self._resume_watch_after = None

        self._resume_watch_after = self.root.after(2000, tick)

    def _shutdown_app(self):
        """Chiude l'app senza lasciare popup/grab che possano bloccare la GUI."""
        try:
            aid = getattr(self, "_resume_watch_after", None)
            if aid is not None:
                self.root.after_cancel(aid)
        except Exception:
            pass
        self._resume_watch_after = None

        # Sicurezza GUI: un vecchio dialogo non deve mai trattenere il grab
        # e impedire al pulsante ESCI di chiudere l'applicazione.
        try:
            grabbed = self.root.grab_current()
            if grabbed is not None:
                grabbed.grab_release()
        except Exception:
            pass

        for _name in ("_export_save_dialog", "_export_capture_window"):
            try:
                _w = getattr(self, _name, None)
                if _w is not None and _w.winfo_exists():
                    try:
                        _w.grab_release()
                    except Exception:
                        pass
                    _w.destroy()
            except Exception:
                pass
            try:
                setattr(self, _name, None)
            except Exception:
                pass

        self._release_suspend_inhibitor(force=True)
        try:
            self.root.destroy()
        except Exception:
            pass

    def refresh_interfaces(self, preferred=None):
        names,types=self.get_interfaces()
        monitors=[n for n in names if types.get(n)=="monitor"]
        others=[n for n in names if n not in monitors]
        vals=monitors + others

        self.iface_combo["values"]=vals

        current=self.iface.get().strip()
        if preferred and preferred in vals:
            self.iface.set(preferred)
        elif current in vals:
            self.iface.set(current)
        elif monitors:
            self.iface.set(monitors[0])
        elif vals:
            self.iface.set(vals[0])
        else:
            self.iface.set("")

        self._update_iface_origin()

        self.logmsg(
            "Interfacce rilevate: "
            + ", ".join(
                f"{n} [{types.get(n,'?')}] "
                f"[{'USB ESTERNA' if self.is_usb_network_interface(n) else 'PC/INTERNA'}]"
                for n in names
            )
        )

    def interface_supports_monitor_mode(self, iface):
        """
        Verifica dal PHY associato all'interfaccia se il driver dichiara
        il supporto alla modalità monitor.
        """
        iface=(iface or "").strip()
        if not iface:
            return False, "Interfaccia non valida"

        try:
            p=run(["iw","dev",iface,"info"], timeout=6)
        except Exception as e:
            return False, f"Errore lettura PHY: {e}"

        if p.returncode != 0:
            detail=(p.stderr or p.stdout or "").strip()
            return False, detail or "Impossibile determinare il PHY dell'interfaccia"

        m=re.search(r"wiphy\s+(\d+)", p.stdout or "")
        if not m:
            return False, "PHY non identificato"

        phy="phy"+m.group(1)

        try:
            info=run(["iw","phy",phy,"info"], timeout=8)
        except Exception as e:
            return False, f"Errore verifica capacità monitor: {e}"

        if info.returncode != 0:
            detail=(info.stderr or info.stdout or "").strip()
            return False, detail or "Impossibile leggere le modalità supportate"

        out=info.stdout or ""
        supported=False
        in_modes=False
        for line in out.splitlines():
            stripped=line.strip()
            if stripped.startswith("Supported interface modes:"):
                in_modes=True
                continue
            if in_modes:
                if not stripped:
                    break
                if stripped.startswith("*"):
                    mode=stripped.lstrip("*").strip().lower()
                    if mode == "monitor":
                        supported=True
                        break
                elif not line.startswith((" ","\t")):
                    break

        if supported:
            return True, f"{phy}: modalità monitor supportata"
        return False, f"{phy}: il driver non dichiara la modalità monitor"

    def _set_monitor_mode_visible_state(self, iface, active):
        if active:
            self.active_monitor_iface=(iface or "").strip()
            self.monitor_mode_state.set("MONITOR MODE: ON")
            try:
                self.monitor_mode_label.configure(bg="#2E7D32", fg="#FFFFFF")
            except Exception:
                pass
        else:
            self.active_monitor_iface=""
            self.monitor_mode_state.set("MONITOR MODE: OFF")
            try:
                self.monitor_mode_label.configure(bg="#FF0000", fg="#FFFFFF")
            except Exception:
                pass

    def enable_monitor_mode(self):
        """
        Kali Live / doppia Wi-Fi - modalità diretta sulla SOLA scheda USB.

        Questa versione NON crea wlanXmon e NON usa airmon-ng/rfkill.
        Sgancia soltanto la scheda USB selezionata da NetworkManager,
        la converte direttamente da managed -> monitor e lascia intatta
        ogni altra interfaccia (es. wlan0 interna).

        È pensata per chipset/driver che dichiarano #channels <= 1 e che
        lavorano meglio con una sola interfaccia sul PHY.
        """
        if not self.check_deps():
            return

        iface=(self.iface.get() or "").strip()
        names,types=self.get_interfaces()

        if not iface or iface not in names:
            messagebox.showerror(
                "Monitor mode",
                "Seleziona prima una interfaccia Wi-Fi valida."
            )
            return

        # Non toccare mai la scheda interna: richiedi esplicitamente una USB.
        if not self.is_usb_network_interface(iface):
            messagebox.showerror(
                "Monitor mode",
                f"{iface} non risulta una scheda Wi-Fi USB esterna.\n\n"
                "Seleziona la scheda USB. La Wi-Fi interna del PC non verrà modificata."
            )
            return

        def is_monitor(name):
            p=run(["iw","dev",name,"info"], timeout=6)
            txt=(p.stdout or "") + "\n" + (p.stderr or "")
            return p.returncode == 0 and bool(
                re.search(r"(?mi)^\s*type\s+monitor\s*$", txt)
            )

        if is_monitor(iface):
            self.active_monitor_iface=iface
            self._set_monitor_mode_visible_state(iface, True)
            self.refresh_interfaces(preferred=iface)
            self.set_status(f"MONITOR MODE CONFERMATA su {iface}")
            return

        supported,detail=self.interface_supports_monitor_mode(iface)
        self.logmsg(f"Supporto monitor {iface}: {detail}")
        if not supported:
            self._set_monitor_mode_visible_state("", False)
            messagebox.showerror(
                "Monitor mode non supportata",
                f"{iface}: {detail}"
            )
            return

        self.monitor_mode_state.set("MONITOR MODE: ATTIVAZIONE")
        self.set_status(f"Attivazione monitor mode SOLO su {iface}...")

        # 1) Scollega SOLO la scheda USB selezionata.
        if shutil.which("nmcli"):
            self.logmsg(f"$ nmcli device disconnect {iface}")
            nm=run(["nmcli","device","disconnect",iface], timeout=10)
            if nm.stdout:
                self.logmsg("nmcli: " + nm.stdout.strip())
            if nm.stderr:
                self.logmsg("nmcli STDERR: " + nm.stderr.strip())

            # Dice a NetworkManager di non riprendersi SOLO questa scheda.
            self.logmsg(f"$ nmcli device set {iface} managed no")
            nm2=run(["nmcli","device","set",iface,"managed","no"], timeout=10)
            if nm2.stdout:
                self.logmsg("nmcli: " + nm2.stdout.strip())
            if nm2.stderr:
                self.logmsg("nmcli STDERR: " + nm2.stderr.strip())

        time.sleep(0.8)

        # 2) Conversione diretta della sola USB: nessuna VIF aggiuntiva.
        sequence=[
            ["ip","link","set",iface,"down"],
            ["iw","dev",iface,"set","type","monitor"],
            ["ip","link","set",iface,"up"],
        ]

        failed=None
        for cmd in sequence:
            self.logmsg("$ " + " ".join(cmd))
            p=run(cmd, timeout=10)
            if p.stdout:
                self.logmsg("OUTPUT: " + p.stdout.strip())
            if p.stderr:
                self.logmsg("STDERR: " + p.stderr.strip())
            if p.returncode != 0:
                failed=(cmd,p)
                break

        # 3) Verifica forte con iw: deve essere davvero type monitor.
        if failed is None:
            for _ in range(12):
                time.sleep(0.3)
                if is_monitor(iface):
                    self.active_monitor_iface=iface
                    self.iface.set(iface)
                    self._set_monitor_mode_visible_state(iface, True)
                    self.refresh_interfaces(preferred=iface)
                    self.set_status(f"MONITOR MODE CONFERMATA su {iface}")
                    self.logmsg(
                        f"MONITOR DIRETTA OK: {iface}=type monitor; "
                        "le altre interfacce Wi-Fi non sono state modificate."
                    )
                    return

        # 4) Rollback della SOLA USB se qualcosa non funziona.
        self.logmsg(f"MONITOR FALLITO: ripristino esclusivamente {iface} in managed.")
        try:
            run(["ip","link","set",iface,"down"], timeout=6)
            run(["iw","dev",iface,"set","type","managed"], timeout=8)
            run(["ip","link","set",iface,"up"], timeout=6)
        except Exception:
            pass

        if shutil.which("nmcli"):
            try:
                run(["nmcli","device","set",iface,"managed","yes"], timeout=8)
                run(["nmcli","device","connect",iface], timeout=12)
            except Exception:
                pass

        self._set_monitor_mode_visible_state("", False)
        self.refresh_interfaces(preferred=iface)
        self.set_status("MONITOR MODE NON ATTIVA.")

        if failed is not None:
            cmd,p=failed
            detail=(p.stderr or p.stdout or f"exit={p.returncode}").strip()
            messagebox.showerror(
                "Monitor mode",
                f"Errore sul comando:\n{' '.join(cmd)}\n\n{detail}\n\n"
                "La sola scheda USB è stata ripristinata in managed."
            )
        else:
            messagebox.showerror(
                "Monitor mode",
                f"{iface} non risulta in type monitor dopo il tentativo.\n\n"
                "La sola scheda USB è stata ripristinata in managed."
            )


    def validate_monitor_iface(self):
        """Verifica la monitor mode usando come fonte primaria `iw`."""
        if not self.check_deps():
            return None

        candidates=[]
        if self.active_monitor_iface:
            candidates.append(self.active_monitor_iface)

        selected=(self.iface.get() or "").strip()
        if selected and selected not in candidates:
            candidates.append(selected)

        names,types=self.get_interfaces()
        for n in names:
            if types.get(n)=="monitor" and n not in candidates:
                candidates.append(n)

        for iface in candidates:
            p=run(["iw","dev",iface,"info"], timeout=6)
            txt=(p.stdout or "") + "\n" + (p.stderr or "")
            if p.returncode == 0 and re.search(r"(?mi)^\s*type\s+monitor\s*$", txt):
                self.active_monitor_iface=iface
                self.iface.set(iface)
                self._set_monitor_mode_visible_state(iface, True)
                self.refresh_interfaces(preferred=iface)
                return iface

        self._set_monitor_mode_visible_state("", False)
        messagebox.showerror(
            "Monitor mode",
            "Nessuna interfaccia risulta in monitor mode."
        )
        return None


    def _set_scan_progress(self, which, value):
        value=max(0.0,min(100.0,float(value)))
        if which=="ap":
            self.root.after(0, self.ap_scan_progress.set, value)
            self.root.after(0, self.ap_scan_progress_text.set, f"{value:.0f}%")
        elif which=="client":
            self.root.after(0, self.client_scan_progress.set, value)
            self.root.after(0, self.client_scan_progress_text.set, f"{value:.0f}%")

    def _progress_during_wait(self, which, seconds, start_pct, end_pct, stop_event, pause_event=None):
        """
        Avanzamento fluido delle barre blu router/client.
        Se pause_event è attivo, la barra resta congelata e riprende dallo stesso punto.
        """
        start=time.monotonic()
        paused_total=0.0
        pause_started=None
        seconds=max(0.1,float(seconds))

        while not stop_event.is_set():
            if pause_event is not None and pause_event.is_set():
                if pause_started is None:
                    pause_started=time.monotonic()
                time.sleep(0.05)
                continue

            if pause_started is not None:
                paused_total += time.monotonic() - pause_started
                pause_started=None

            elapsed=min(seconds,time.monotonic()-start-paused_total)
            frac=elapsed/seconds
            value=start_pct + (end_pct-start_pct)*frac
            self._set_scan_progress(which,value)
            if elapsed >= seconds:
                break
            time.sleep(0.05)


    def _ap_sort_value(self, column, value):
        """Valore normalizzato e stabile per ordinare le colonne ROUTER."""
        txt = str(value or "").strip()

        if column == "band":
            low = txt.lower().replace(",", ".")
            if "6" in low and "ghz" in low:
                return 6.0
            if "5" in low and "ghz" in low:
                return 5.0
            if "2.4" in low and "ghz" in low:
                return 2.4
            return -1.0

        if column in ("packets", "clients"):
            try:
                return int(float(txt))
            except Exception:
                return -1

        if column == "pwr":
            # airodump usa valori negativi: -30 è più forte/grande di -80.
            try:
                return float(txt)
            except Exception:
                return -9999.0

        return txt.casefold()


    def _reset_ap_manual_sort(self, reorder_live=True):
        """Rimuove frecce/ordinamento manuale e torna all'ordine live normale."""
        self.ap_manual_sort_column = None
        self.ap_manual_sort_desc = True

        try:
            for col in ("band", "packets", "pwr", "clients"):
                txt = str(self.ap_tree.heading(col, "text") or "")
                txt = txt.replace(" ▼", "").replace(" ▲", "")
                self.ap_tree.heading(col, text=txt)
        except Exception:
            pass

        if reorder_live:
            try:
                self._reorder_ap_tree_pre201_grouped()
            except Exception:
                pass

    def _sort_ap_tree_by_heading(self, column):
        """
        Ordina BANDA/PACCHETTI/POTENZA/CLIENTI soltanto a scansione
        terminata o temporaneamente in pausa.

        Primo clic sulla colonna: grande -> piccolo.
        Secondo clic: piccolo -> grande.
        I clic successivi continuano ad alternare.
        """
        if column not in ("band", "packets", "pwr", "clients"):
            return

        try:
            paused = self.ap_scan_pause.is_set()
        except Exception:
            paused = False

        if not (getattr(self, "ap_scan_finished", True) or paused):
            try:
                self.set_status(
                    "Metti in pausa o attendi la fine della scansione per ordinare."
                    if getattr(self, "language", "it") != "en"
                    else
                    "Pause the scan or wait for it to finish before sorting."
                )
            except Exception:
                pass
            return

        descending = True
        if self.ap_manual_sort_column == column:
            descending = not bool(self.ap_manual_sort_desc)

        cols = list(self.ap_tree["columns"])
        try:
            idx = cols.index(column)
        except ValueError:
            return

        rows = []
        for original_pos, item in enumerate(self.ap_tree.get_children()):
            vals = self.ap_tree.item(item, "values")
            value = vals[idx] if len(vals) > idx else ""
            norm = self._ap_sort_value(column, value)
            rows.append((norm, original_pos, item))

        # Stable sort: Python mantiene l'ordine originale per valori uguali.
        rows.sort(key=lambda rec: rec[0], reverse=descending)

        for new_pos, (_value, _old_pos, item) in enumerate(rows):
            try:
                self.ap_tree.move(item, "", new_pos)
            except Exception:
                pass

        self.ap_manual_sort_column = column
        self.ap_manual_sort_desc = descending

        try:
            for col in ("band", "packets", "pwr", "clients"):
                txt = str(self.ap_tree.heading(col, "text") or "")
                txt = txt.replace(" ▼", "").replace(" ▲", "")
                if col == column:
                    txt += " ▼" if descending else " ▲"
                self.ap_tree.heading(col, text=txt)
        except Exception:
            pass


    def stop_ap_scan(self):
        """
        Toggle PAUSA/CONTINUA della scansione ROUTER RILEVATI.
        Finché la barra non è al 100%, il pulsante alterna:
          STOP RICERCA -> mette in pausa
          CONTINUA     -> riprende
        Al 100% non fa più nulla.
        """
        if getattr(self, "ap_scan_finished", True):
            return

        proc=getattr(self, "ap_scan_process", None)
        if proc is None or proc.poll() is not None:
            return

        btn=getattr(self, "stop_ap_scan_button", None)

        if not self.ap_scan_pause.is_set():
            # PAUSA reale del processo airodump-ng: non termina la scansione.
            try:
                os.killpg(proc.pid, signal.SIGSTOP)
            except Exception:
                try:
                    proc.send_signal(signal.SIGSTOP)
                except Exception as e:
                    self.logmsg(f"Impossibile mettere in pausa la scansione router: {e}")
                    return

            self.ap_scan_pause.set()
            try:
                self._set_operation_mode_banner("idle")
            except Exception:
                pass
            if btn is not None:
                try:
                    btn.configure(text="CONTINUA")
                except Exception:
                    pass
            self.set_status("Scansione router in pausa.")
            self.logmsg("STOP RICERCA: scansione router messa in pausa.")
        else:
            # Riprende esattamente lo stesso processo.
            try:
                os.killpg(proc.pid, signal.SIGCONT)
            except Exception:
                try:
                    proc.send_signal(signal.SIGCONT)
                except Exception as e:
                    self.logmsg(f"Impossibile riprendere la scansione router: {e}")
                    return

            self.ap_scan_pause.clear()

            # Ripresa scansione: torna immediatamente all'ordine live e gli
            # aggiornamenti successivi continuano a riordinare i risultati.
            self._reset_ap_manual_sort(reorder_live=True)

            try:
                self._set_operation_mode_banner("passive")
            except Exception:
                pass
            if btn is not None:
                try:
                    btn.configure(text="STOP RICERCA")
                except Exception:
                    pass
            self.set_status("Scansione router ripresa.")
            self.logmsg("CONTINUA: scansione router ripresa.")

    @staticmethod
    def _power_sort_value(value):
        """Converte PWR in intero; valori non validi vanno in fondo."""
        try:
            p = int(float(str(value).strip()))
        except Exception:
            return -9999
        if p in (0, -1):
            return -9999
        return p

    def _sort_aps_grouped_pre201(self, aps):
        """
        Ordinamento richiesto:
        - POTENZA più alta in cima;
        - stesso ESSID sempre raggruppato (es. 2.4 + 5 GHz);
        - il gruppo prende la posizione dalla sua radio con POTENZA migliore;
        - dentro lo stesso ESSID: POTENZA decrescente, poi banda/canale.
        """
        rows = list(aps or [])
        groups = {}

        for ap in rows:
            try:
                bssid, ch, enc, pwr, essid, packets = ap
                essid_text = str(essid or "").strip()
                low = essid_text.casefold()
                hidden = (
                    not essid_text
                    or low in {
                        "<hidden>", "<ssid nascosto>", "<ssid hidden>",
                        "<sconosciuto>", "hidden", "(hidden)"
                    }
                )
                # Gli SSID nascosti non vanno fusi tra loro.
                key = (
                    f"__hidden__:{str(bssid).lower()}:{str(ch)}"
                    if hidden else f"ssid:{low}"
                )
                groups.setdefault(key, []).append(ap)
            except Exception:
                pass

        def band_order(ch):
            band = self.band_from_channel(ch)
            return {
                "2.4 GHz": 0, "2,4 GHz": 0,
                "5 GHz": 1, "5.8 GHz": 1,
                "6 GHz": 2
            }.get(band, 9)

        # Prima i gruppi il cui AP più forte ha PWR maggiore.
        ordered_groups = sorted(
            groups.values(),
            key=lambda group: (
                max(self._power_sort_value(x[3]) for x in group),
                str(group[0][4] or "").casefold()
            ),
            reverse=True
        )

        result = []
        for group in ordered_groups:
            # All'interno dello stesso SSID mantiene prima la radio più potente.
            group.sort(
                key=lambda x: (
                    -self._power_sort_value(x[3]),
                    band_order(x[1]),
                    int(x[1]) if str(x[1]).isdigit() else 9999,
                    str(x[0]).lower()
                )
            )
            result.extend(group)

        return result

    def _reorder_ap_tree_pre201_grouped(self):
        """Riapplica l'ordine verticale pre-v201 mantenendo vicini gli ESSID uguali."""
        rows = []
        item_by_key = {}

        for item in self.ap_tree.get_children():
            vals = self.ap_tree.item(item, "values")
            if not vals or len(vals) < 8:
                continue
            bssid, ch, pwr, essid, band, clients, packets, enc = vals[:8]
            ap = (bssid, ch, enc, pwr, essid, packets)
            rows.append(ap)
            item_by_key[(str(bssid).lower(), str(ch), str(band))] = item

        ordered = self._sort_aps_grouped_pre201(rows)

        for index, ap in enumerate(ordered):
            bssid, ch, enc, pwr, essid, packets = ap
            band = self.band_from_channel(ch)
            item = item_by_key.get((str(bssid).lower(), str(ch), str(band)))
            if item:
                try:
                    self.ap_tree.move(item, "", index)
                except Exception:
                    pass

    def _upsert_ap_rows_live(self, aps):
        """
        Aggiorna in-place router e PACCHETTI senza cancellare la tabella.
        La chiave include BSSID + canale + banda: in questo modo eventuali
        righe dello stesso BSSID su canali/bande diversi restano indipendenti.
        """
        existing = {}
        for item in self.ap_tree.get_children():
            vals = self.ap_tree.item(item, "values")
            if not vals:
                continue
            try:
                key = (
                    str(vals[0]).lower(),
                    str(vals[1]),
                    str(vals[4])
                )
                existing[key] = item
            except Exception:
                pass

        # Ordine live: potenza più alta in cima, ma stesso ESSID sempre raggruppato.
        aps = self._sort_aps_grouped_pre201(aps)

        seen = set()
        for ap in aps or []:
            try:
                bssid, ch, enc, pwr, essid, packets = ap
            except Exception:
                continue

            bssid_l = str(bssid).lower()
            ch_s = str(ch)
            band = self.band_from_channel(ch_s)
            key = (bssid_l, ch_s, str(band))
            seen.add(key)

            clients = self.ap_client_counts.get(bssid_l, 0)
            row = (bssid, ch_s, pwr, essid, band, clients, packets, enc)

            # Snapshot persistente usato dal controllo dual-band anche se la
            # Treeview viene successivamente riordinata/aggiornata.
            if not hasattr(self, "_dual_band_ap_snapshot"):
                self._dual_band_ap_snapshot = {}
            self._dual_band_ap_snapshot[(bssid_l, ch_s, str(band))] = tuple(row)

            item = existing.get(key)
            if item:
                # Aggiorna l'intera riga, compresa la colonna PACCHETTI.
                self.ap_tree.item(item, values=row)
            else:
                item = self.ap_tree.insert("", "end", values=row)
                existing[key] = item

        # Le righe esistenti vanno anche fisicamente spostate.
        # Se la scansione è attiva, l'ordine manuale è annullato e prevale
        # sempre l'ordine live aggiornato.
        if not getattr(self, "ap_scan_finished", True) and not self.ap_scan_pause.is_set():
            self._reset_ap_manual_sort(reorder_live=False)
            self._reorder_ap_tree_pre201_grouped()
        elif self.ap_manual_sort_column is None:
            self._reorder_ap_tree_pre201_grouped()

        self.router_count.set(
            ("Count: " if getattr(self, "language", "it") == "en" else "Numero: ")
            + str(len(seen))
        )

    def _update_ap_client_counts_live(self, counts):
        """Aggiorna in tempo reale il numero client associati per BSSID."""
        if not counts:
            return
        cols = list(self.ap_tree["columns"])
        try:
            ci = cols.index("clients")
        except ValueError:
            return

        for bssid, stations in counts.items():
            self.ap_client_counts[bssid] = len(stations)

        for item in self.ap_tree.get_children():
            vals = list(self.ap_tree.item(item, "values"))
            if not vals:
                continue
            bssid = str(vals[0]).lower()
            if bssid not in counts:
                continue
            while len(vals) < len(cols):
                vals.append("")
            vals[ci] = len(counts[bssid])
            self.ap_tree.item(item, values=vals)

    def _upsert_client_rows_live(self, rows, source=None):
        """Aggiorna i client in modo cumulativo, mantenendo la provenienza della singola scansione."""
        # La provenienza viene passata dal worker che ha prodotto le righe.
        # In questo modo una scansione correlata avviata successivamente non può
        # cambiare retroattivamente il BSSID/SSID/canale delle righe precedenti.
        if source is None:
            source = getattr(self, "_client_current_source_label", "")
        source = str(source or "").strip()

        existing = {}
        for item in self.client_tree.get_children():
            vals = tuple(self.client_tree.item(item, "values") or ())
            if not vals:
                continue
            sta = str(vals[0]).lower()
            src = str(vals[6] if len(vals) > 6 else "")
            existing[(sta, src)] = item

        unique = {}
        for row in rows or []:
            if not row:
                continue
            sta = str(row[0]).lower()
            vals = tuple(row[:6]) + (source,)
            unique[(sta, source)] = vals

        for key, row in unique.items():
            item = existing.get(key)
            if item:
                self.client_tree.item(item, values=row)
            else:
                existing[key] = self.client_tree.insert("", "end", values=row)

        # Il contatore rappresenta tutte le righe conservate: prima scansione +
        # eventuali BSSID correlati. Lo stesso MAC può comparire più volte se
        # realmente osservato da provenienze diverse.
        try:
            prefix = "Count: " if getattr(self, "language", "it") == "en" else "Numero: "
            self.client_count.set(prefix + str(len(self.client_tree.get_children())))
        except Exception:
            pass

        if not self.client_scan_pause.is_set():
            self._reset_client_manual_sort(reorder_live=False)
            self._sort_client_tree_by_packets()

        total = len(self.client_tree.get_children())
        current = len(unique)
        if total > current:
            self.client_count.set(
                (f"Count: {total} | CURRENT: {current}"
                 if getattr(self, "language", "it") == "en"
                 else f"Numero: {total} | CORRENTE: {current}")
            )
        else:
            self.client_count.set(
                ("Count: " if getattr(self, "language", "it") == "en" else "Numero: ")
                + str(total)
            )

        try:
            if getattr(self, "live_mac_rows", None):
                self.update_probable_lan_vendors(list(self.live_mac_rows.values()))
        except Exception:
            pass
        try:
            self._merge_camera_candidates_from_client_scan(
                rows,
                getattr(self, "_client_current_source_bssid", ""),
                self._dual_band_value(getattr(self, "channel", ""))
            )
        except Exception:
            pass

        try:
            self._refresh_camera_block_action()
        except Exception:
            pass

    def _clear_all_scan_results(self):
        """Azzera tutti i risultati visibili prima di una nuova scansione reti Wi-Fi."""
        # Prima di pulire la GUI conserva lo stato corrente. La memoria del
        # grafico dura dall'apertura alla chiusura del programma e NON viene azzerata.
        try:
            _gp = self._dual_band_value(getattr(self, "bssid", ""))
        except Exception:
            _gp = ""
        try:
            self._network_graph_snapshot_current(_gp, "before new Wi-Fi scan")
        except Exception:
            pass
        # ROUTER RILEVATI
        for tree_name in ("ap_tree", "client_tree", "lan_vendor_tree", "res_tree"):
            tree = getattr(self, tree_name, None)
            if tree is None:
                continue
            try:
                for item in tree.get_children():
                    tree.delete(item)
            except Exception:
                pass

        # Contatori e cache collegate ai risultati visualizzati.
        try:
            self.router_count.set("Numero: 0")
        except Exception:
            pass
        try:
            self.client_count.set("Numero: 0")
        except Exception:
            pass
        try:
            self.probable_lan_vendor_count.set("Numero: 0")
        except Exception:
            pass
        try:
            self.lan_count.set("LAN candidati: 0")
            self.other_count.set("Altro/incerto: 0")
        except Exception:
            pass

        self.ap_client_counts = {}

        # Elimina anche le vecchie selezioni/didascalie legate alla scansione precedente.
        try:
            self.bssid.set("")
            self.client.set("")
            self.channel.set("")
            self.client_search_caption.set("Ricerca Client Associati a: --")
            self.block_router_value.set("")
            self.block_client_value.set("")

            self._update_capture_panel_titles()
        except Exception:
            pass

        # Azzera le due barre di scansione; la barra router ripartirà subito dopo.
        try:
            self._set_scan_progress("ap", 0)
            self._set_scan_progress("client", 0)
        except Exception:
            pass

        self.logmsg(
            "Nuova scansione Wi-Fi: cancellati risultati precedenti "
            "(router, client, LAN e MAC catturati)."
        )

    def scan_aps(self):
        # Se la scansione router è già in corso o in pausa, il pulsante
        # SCANSIONA ROUTER non deve avviare una seconda cattura.
        # L'unico controllo consentito durante il lavoro è STOP/CONTINUA.
        if not getattr(self, "ap_scan_finished", True):
            self.set_status(
                "Router scan already running: use STOP/CONTINUE and wait for 100%."
                if getattr(self, "language", "it") == "en"
                else "Scansione router già in corso: usa STOP/CONTINUA e attendi il 100%."
            )
            return

        iface=self.validate_monitor_iface()
        if not iface:
            return
        self._set_operation_mode_banner("passive")
        self._acquire_suspend_inhibitor("ap-scan")

        # Ogni nuova SCANSIONE RETI WIFI riparte completamente da zero.
        # 1) pulisce tutte le tabelle/finestre dati;
        self._clear_all_scan_results()

        # 2) riporta il quadro HANDSHAKE allo stato iniziale;
        self.handshake_pairs.clear()
        self.handshake_found_async=False
        self.handshake_latched=False
        self.handshake_latched_text=""
        self.handshake_latched_msgs=set()
        self._reset_handshake_panel()
        try:
            self.pmkid_state.set("PMKID: non osservato")
        except Exception:
            pass

        # 3) i due pulsanti di esportazione tornano grigi/non cliccabili.
        self._set_export_button_enabled("capture", False)
        self._set_export_button_enabled("handshake", False)

        # 4) azzera anche l'avanzamento della cattura precedente.
        self.set_progress(
            0,
            "0%",
            "PRONTO",
            "Nuova scansione reti Wi-Fi"
        )

        self.ap_scan_stop.clear()
        self.ap_scan_pause.clear()
        self._reset_ap_manual_sort(reorder_live=False)
        self.ap_scan_finished=False
        self.ap_scan_process=None
        try:
            self.stop_ap_scan_button.configure(state="normal",text="STOP RICERCA")
        except Exception:
            pass
        self._set_scan_progress("ap",0)
        self._start_button_blink("scan_wifi_button")
        threading.Thread(target=self._scan_worker,args=(iface,),daemon=True).start()

    def _scan_worker(self,iface):
        self.set_status("Scansione router: pacchetti aggiornati in tempo reale...")
        self._set_scan_progress("ap",0)

        stamp=datetime.now().strftime("%Y%m%d_%H%M%S")
        prefix=self.outdir/f"scan_{stamp}"
        csvfile=Path(str(prefix)+"-01.csv")

        cmd=["airodump-ng","--band","abg","--write",str(prefix),"--write-interval","1","--output-format","csv",iface]
        self.logmsg("$ "+" ".join(cmd))

        try:
            proc=popen_logged(
                cmd,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                text=True,
                start_new_session=True
            )
            self.ap_scan_process=proc
        except Exception as e:
            self.set_status(f"Errore scansione router: {e}")
            self.ap_scan_finished=True
            self.root.after(0, lambda: self.stop_ap_scan_button.configure(state="disabled",text="STOP RICERCA"))
            self._stop_button_blink("scan_wifi_button")
            self._set_operation_mode_banner("idle")
            self._release_suspend_inhibitor_later("ap-scan")
            return

        duration=20.0
        active_elapsed=0.0
        last_tick=time.monotonic()
        self.ap_scan_finished=False
        self.ap_scan_pause.clear()
        self.root.after(0, lambda: self.stop_ap_scan_button.configure(state="normal",text="STOP RICERCA"))

        try:
            while True:
                now=time.monotonic()
                delta=max(0.0,now-last_tick)
                last_tick=now

                if not self.ap_scan_pause.is_set():
                    active_elapsed += delta

                    # Aggiornamento dati solo mentre la scansione è attiva.
                    if csvfile.exists():
                        try:
                            aps,_=self.parse_airodump_csv(csvfile)
                            counts=self.parse_client_counts_by_bssid(csvfile)
                            self.root.after(0, lambda data=list(aps): self._upsert_ap_rows_live(data))
                            self.root.after(
                                0,
                                lambda data={k:set(v) for k,v in counts.items()}:
                                    self._update_ap_client_counts_live(data)
                            )
                        except Exception as e:
                            self.logmsg(f"Aggiornamento live router: {e}")

                    pct=min(100.0,(active_elapsed/duration)*100.0)
                    self._set_scan_progress("ap",pct)

                if active_elapsed >= duration or proc.poll() is not None:
                    break

                # ap_scan_stop resta disponibile come hard-stop interno/chiusura,
                # ma il pulsante GUI STOP non lo usa più.
                if self.ap_scan_stop.is_set():
                    break

                time.sleep(0.05)
        finally:
            # Se si chiude/finisce mentre era in SIGSTOP, riprende prima di terminare.
            if self.ap_scan_pause.is_set() and proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGCONT)
                except Exception:
                    pass
                self.ap_scan_pause.clear()

            if proc.poll() is None:
                try:
                    proc.terminate()
                    proc.wait(timeout=2)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
            self.ap_scan_process=None

        if csvfile.exists():
            try:
                aps,_=self.parse_airodump_csv(csvfile)
                counts=self.parse_client_counts_by_bssid(csvfile)
                self.root.after(0, lambda data=list(aps): self._upsert_ap_rows_live(data))
                self.root.after(
                    0,
                    lambda data={k:set(v) for k,v in counts.items()}:
                        self._update_ap_client_counts_live(data)
                )
            except Exception as e:
                self.logmsg(f"Lettura finale router: {e}")

        self.ap_scan_finished=True
        if active_elapsed >= duration and not self.ap_scan_stop.is_set():
            self._set_scan_progress("ap",100)
            self.set_status("Scansione router completata.")
        else:
            self.set_status("Scansione router arrestata.")

        self.root.after(
            0,
            lambda: self.stop_ap_scan_button.configure(
                state="disabled",
                text="STOP RICERCA"
            )
        )
        self._stop_button_blink("scan_wifi_button")
        self._release_suspend_inhibitor_later("ap-scan")
        self._set_operation_mode_banner("idle")

    def _client_heading_sort_value(self, column, value):
        """Normalizza i valori delle colonne CLIENT per un ordinamento coerente."""
        txt = str(value or "").strip()

        if column in ("pwr", "packets"):
            try:
                return float(txt)
            except Exception:
                return -999999.0

        return txt.casefold()


    def _reset_client_manual_sort(self, reorder_live=True):
        """Rimuove il sort manuale e ripristina l'ordinamento live per pacchetti."""
        self.client_manual_sort_column = None
        self.client_manual_sort_desc = True

        try:
            for col in ("station", "resolved", "vendor", "pwr", "packets", "probes"):
                txt = str(self.client_tree.heading(col, "text") or "")
                txt = txt.replace(" ▼", "").replace(" ▲", "")
                self.client_tree.heading(col, text=txt)
        except Exception:
            pass

        if reorder_live:
            try:
                self._sort_client_tree_by_packets()
            except Exception:
                pass

    def _sort_client_tree_by_heading(self, column):
        """
        Ordina la tabella CLIENT soltanto quando la scansione è in pausa o terminata.
        Primo clic: grande->piccolo / Z->A.
        Secondo clic: piccolo->grande / A->Z.
        """
        if column not in ("station", "resolved", "vendor", "pwr", "packets", "probes"):
            return

        try:
            paused = self.client_scan_pause.is_set()
        except Exception:
            paused = False

        if not (getattr(self, "client_scan_finished", True) or paused):
            try:
                self.set_status(
                    "Metti in pausa o attendi la fine della ricerca client per ordinare."
                    if getattr(self, "language", "it") != "en"
                    else
                    "Pause the client scan or wait for it to finish before sorting."
                )
            except Exception:
                pass
            return

        descending = True
        if self.client_manual_sort_column == column:
            descending = not bool(self.client_manual_sort_desc)

        cols = list(self.client_tree["columns"])
        try:
            idx = cols.index(column)
        except ValueError:
            return

        rows = []
        for original_pos, item in enumerate(self.client_tree.get_children()):
            vals = self.client_tree.item(item, "values")
            value = vals[idx] if len(vals) > idx else ""
            norm = self._client_heading_sort_value(column, value)
            rows.append((norm, original_pos, item))

        rows.sort(key=lambda rec: rec[0], reverse=descending)

        for new_pos, (_value, _old_pos, item) in enumerate(rows):
            try:
                self.client_tree.move(item, "", new_pos)
            except Exception:
                pass

        self.client_manual_sort_column = column
        self.client_manual_sort_desc = descending

        try:
            for col in ("station", "resolved", "vendor", "pwr", "packets", "probes"):
                txt = str(self.client_tree.heading(col, "text") or "")
                txt = txt.replace(" ▼", "").replace(" ▲", "")
                if col == column:
                    txt += " ▼" if descending else " ▲"
                self.client_tree.heading(col, text=txt)
        except Exception:
            pass


    def stop_client_scan(self):
        try:
            _dual_client_bssid = self._dual_band_value(getattr(self,"bssid",""))
            _dual_client_channel = self._dual_band_value(getattr(self,"channel",""))
        except Exception:
            _dual_client_bssid, _dual_client_channel = "", ""
        """
        Toggle PAUSA/CONTINUA della scansione CLIENT.
        Usa SIGSTOP/SIGCONT sullo stesso processo airodump-ng.
        """
        if getattr(self, "client_scan_finished", True):
            return

        proc=getattr(self, "client_scan_process", None)
        if proc is None or proc.poll() is not None:
            return

        btn=getattr(self, "stop_client_scan_button", None)

        if not self.client_scan_pause.is_set():
            try:
                os.killpg(proc.pid, signal.SIGSTOP)
            except Exception:
                try:
                    proc.send_signal(signal.SIGSTOP)
                except Exception as e:
                    self.logmsg(
                        f"Unable to pause client scan: {e}"
                        if getattr(self, "language", "it") == "en"
                        else f"Impossibile mettere in pausa la scansione client: {e}"
                    )
                    return

            self.client_scan_pause.set()
            try:
                self._set_operation_mode_banner("idle")
            except Exception:
                pass
            if btn is not None:
                try:
                    btn.configure(
                        text="CONTINUE"
                        if getattr(self, "language", "it") == "en"
                        else "CONTINUA"
                    )
                except Exception:
                    pass
            self.set_status(
                "Client scan paused."
                if getattr(self, "language", "it") == "en"
                else "Scansione client in pausa."
            )

            # Avviso dual-band SOLO quando si preme STOP/PAUSA.
            # Non viene eseguito nel ramo CONTINUA.
            try:
                self._dual_band_watch_client_running = False
                # Una sola chiamata immediata: niente callback ritardate
                # che possano aprire l'avviso dopo aver premuto CONTINUA.
                self.root.after_idle(
                    lambda _b=_dual_client_bssid,_c=_dual_client_channel:
                        self._dual_band_check_after_client_stop(_b,_c)
                )
            except Exception as e:
                try:
                    self.command_debug_write(
                        f"[DUAL-BAND] STOP CLIENT: impossibile pianificare controllo: {e}"
                    )
                except Exception:
                    pass

        else:
            try:
                os.killpg(proc.pid, signal.SIGCONT)
            except Exception:
                try:
                    proc.send_signal(signal.SIGCONT)
                except Exception as e:
                    self.logmsg(
                        f"Unable to resume client scan: {e}"
                        if getattr(self, "language", "it") == "en"
                        else f"Impossibile riprendere la scansione client: {e}"
                    )
                    return

            self.client_scan_pause.clear()
            # Dopo CONTINUA non mostrare alcun avviso, ma riattiva il watcher:
            # servirà SOLO quando la scansione arriverà realmente alla fine.
            self._dual_band_watch_client_running = True
            # Ripresa: i nuovi dati tornano all'ordinamento live automatico.
            self._reset_client_manual_sort(reorder_live=True)
            try:
                self._set_operation_mode_banner("passive")
            except Exception:
                pass
            if btn is not None:
                try:
                    btn.configure(
                        text="STOP SEARCH"
                        if getattr(self, "language", "it") == "en"
                        else "STOP RICERCA"
                    )
                except Exception:
                    pass
            self.set_status(
                "Client scan resumed."
                if getattr(self, "language", "it") == "en"
                else "Scansione client ripresa."
            )


    def scan_clients(self):
        # Se la scansione client è già in corso o in pausa, il pulsante
        # SCANSIONA CLIENT non deve avviare una seconda cattura.
        # L'unico controllo consentito durante il lavoro è STOP/CONTINUA.
        if not getattr(self, "client_scan_finished", True):
            self.set_status(
                "Client scan already running: use STOP/CONTINUE and wait for 100%."
                if getattr(self, "language", "it") == "en"
                else "Scansione client già in corso: usa STOP/CONTINUA e attendi il 100%."
            )
            return

        iface=self.validate_monitor_iface()
        if not iface:
            return
        self._set_scan_progress("client",0)

        bssid=self.bssid.get().strip().lower()
        ch=self.channel.get().strip()
        self._dual_band_last_target = (bssid, ch)
        self._dual_band_watch_client_running = True
        try:
            self.command_debug_write(
                f"[DUAL-BAND] Target CLIENT memorizzato: {bssid} canale {ch}"
            )
        except Exception:
            pass
        if not MAC_FULL.match(bssid):
            messagebox.showwarning("Router","Seleziona prima un router.")
            return
        if not ch.isdigit():
            messagebox.showwarning("Canale","Canale non valido.")
            return

        self._set_operation_mode_banner("passive")
        self._acquire_suspend_inhibitor("client-scan")
        self.client_scan_pause.clear()
        self._reset_client_manual_sort(reorder_live=False)
        self.client_scan_finished = False
        try:
            self.stop_client_scan_button.configure(
                state="normal",
                text=("STOP SEARCH" if self.language == "en" else "STOP RICERCA")
            )
        except Exception:
            pass

        _preserve_client = bool(
            getattr(self, "_client_preserve_previous_for_correlation", False)
        )
        _client_relation = str(
            getattr(self, "_client_next_relation", "") or ""
        )
        if _preserve_client:
            try:
                _prefix = "Count: " if getattr(self, "language", "it") == "en" else "Numero: "
                self.client_count.set(_prefix + str(len(self.client_tree.get_children())))
            except Exception:
                pass
        self._client_current_source_bssid = bssid
        self._client_current_source_label = self._scan_source_label(
            "client", bssid, ch, _client_relation if _preserve_client else ""
        )

        if not _preserve_client:
            for x in self.client_tree.get_children():
                self.client_tree.delete(x)

        self._client_preserve_previous_for_correlation = False
        self._client_next_relation = ""

        self._start_button_blink("scan_client_button")
        threading.Thread(target=self._client_scan_worker,args=(iface,bssid,ch),daemon=True).start()

    def _client_scan_worker(self,iface,bssid,ch):
        self.set_status("Scansione client: pacchetti aggiornati in tempo reale...")
        self._set_scan_progress("client",0)
        # Congela la provenienza di QUESTA scansione: i callback Tk vengono
        # eseguiti dopo e non devono leggere l'etichetta di un eventuale BSSID successivo.
        client_scan_source = str(
            getattr(self, "_client_current_source_label", "") or
            self._scan_source_label("client", bssid, ch, "")
        ).strip()
        stamp=datetime.now().strftime("%Y%m%d_%H%M%S")
        prefix=self.outdir/f"clients_{stamp}"
        csvfile=Path(str(prefix)+"-01.csv")

        run(["iw","dev",iface,"set","channel",ch])
        cmd=[
            "airodump-ng","--bssid",bssid,"--channel",ch,
            "--write",str(prefix),"--write-interval","1","--output-format","csv",iface
        ]
        self.logmsg("$ "+" ".join(cmd))

        try:
            proc=popen_logged(
                cmd,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                text=True,
                start_new_session=True
            )
            self.client_scan_process=proc
            # La scansione CLIENT è realmente partita: memorizza questa radio
            # per evitare di riproporla in futuro per la stessa azione.
            self._dual_band_mark_action_scanned("client", bssid, ch)
        except Exception as e:
            self.set_status(f"Scansione client fallita: {e}")
            self._stop_button_blink("scan_client_button")
            self._release_suspend_inhibitor_later("client-scan")
            self._set_operation_mode_banner("idle")
            self.client_scan_finished = True
            self.client_scan_pause.clear()
            try:
                self.stop_client_scan_button.configure(
                    state="disabled",
                    text=("STOP SEARCH" if self.language == "en" else "STOP RICERCA")
                )
            except Exception:
                pass
            return

        cache=load_vendor_cache()
        duration=20.0
        started=time.monotonic()
        paused_total=0.0
        pause_started=None

        # Barra CLIENT indipendente dal polling CSV:
        # scorre fluida a ~20 Hz, come la barra BLOCCO/CATTURA.
        client_progress_stop = threading.Event()
        threading.Thread(
            target=self._progress_during_wait,
            args=("client", duration, 0, 100, client_progress_stop, self.client_scan_pause),
            daemon=True
        ).start()

        try:
            while True:
                if self.client_scan_pause.is_set():
                    if pause_started is None:
                        pause_started=time.monotonic()
                    time.sleep(0.10)
                    continue

                if pause_started is not None:
                    paused_total += time.monotonic() - pause_started
                    pause_started=None

                elapsed=time.monotonic()-started-paused_total

                if csvfile.exists():
                    try:
                        _,clients=self.parse_airodump_csv(csvfile,target_bssid=bssid)
                        unique={}
                        for c in clients:
                            unique[c["station"].lower()] = c

                        enriched=[]
                        for sta,c in sorted(unique.items()):
                            enriched.append((
                                sta,
                                self.resolve_mac_with_manuf(sta),
                                lookup_vendor(sta,cache),
                                c["power"],
                                c["packets"],
                                c["probes"]
                            ))

                        self.root.after(
                            0,
                            lambda data=list(enriched), src=client_scan_source: self._upsert_client_rows_live(data, src)
                        )

                        band=self.band_from_channel(ch)
                        self.root.after(
                            0,
                            self.update_ap_client_count_display,
                            bssid,
                            len(unique),
                            band
                        )
                    except Exception as e:
                        self.logmsg(f"Aggiornamento live client: {e}")

                if elapsed >= duration or proc.poll() is not None:
                    break
                time.sleep(0.25)
        finally:
            client_progress_stop.set()
            if proc.poll() is None:
                try:
                    proc.terminate()
                    proc.wait(timeout=2)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
            self.client_scan_process=None

        if csvfile.exists():
            try:
                _,clients=self.parse_airodump_csv(csvfile,target_bssid=bssid)
                unique={}
                for c in clients:
                    unique[c["station"].lower()] = c

                enriched=[]
                for sta,c in sorted(unique.items()):
                    enriched.append((
                        sta,
                        self.resolve_mac_with_manuf(sta),
                        lookup_vendor(sta,cache),
                        c["power"],
                        c["packets"],
                        c["probes"]
                    ))
                self.root.after(0, lambda data=list(enriched), src=client_scan_source: self._upsert_client_rows_live(data, src))
                self.root.after(
                    0,
                    lambda: self.client_count.set(
                        ("Count: " if getattr(self, "language", "it") == "en" else "Numero: ")
                        + str(len(self.client_tree.get_children()))
                    )
                )
            except Exception as e:
                self.logmsg(f"Lettura finale client: {e}")

        self._set_scan_progress("client",100)
        self.set_status(f"Scansione client completata per {bssid}.")
        self._stop_button_blink("scan_client_button")
        self._release_suspend_inhibitor_later("client-scan")
        self._set_operation_mode_banner("idle")
        self.client_scan_finished = True
        self.client_scan_pause.clear()
        try:
            self.stop_client_scan_button.configure(
                state="disabled",
                text=("STOP SEARCH" if self.language == "en" else "STOP RICERCA")
            )
        except Exception:
            pass

    def _dual_band_completion_watcher(self):
        """
        Watcher dual-band nel thread GUI.
        Rileva la FINE effettiva di CLIENT e CATTURA senza affidarsi ai worker.
        """
        try:
            bssid, ch = getattr(self, "_dual_band_last_target", ("", ""))
            bssid = self._dual_band_value(bssid)
            ch = self._dual_band_value(ch)

            # CLIENT: avviso alla FINE NATURALE.
            # STOP imposta _dual_band_watch_client_running=False prima di aprire
            # il proprio avviso, quindi il watcher non duplica lo STOP.
            # CONTINUA riattiva il flag quando client_scan_finished è ancora False:
            # perciò nessun avviso viene aperto alla ripartenza.
            if getattr(self, "_dual_band_watch_client_running", False):
                if bool(getattr(self, "client_scan_finished", False)):
                    self._dual_band_watch_client_running = False
                    try:
                        self.command_debug_write(
                            f"[DUAL-BAND] Fine naturale CLIENT: controllo BSSID={bssid} CH={ch}"
                        )
                    except Exception:
                        pass
                    if bssid and ch:
                        self._show_same_bssid_other_band_warning(bssid, ch, "client")

            # CATTURA PASSIVA: start_capture mette il flag True.
            # Quando il banner-lock manuale torna False, la cattura è terminata
            # sia per fine naturale sia per STOP.
            if getattr(self, "_dual_band_watch_capture_running", False):
                capture_active = bool(
                    getattr(self, "_manual_capture_banner_active", False)
                )
                if not capture_active:
                    self._dual_band_watch_capture_running = False
                    try:
                        self.command_debug_write(
                            f"[DUAL-BAND] Fine CATTURA rilevata dal watcher GUI: {bssid} ch {ch}"
                        )
                    except Exception:
                        pass
                    try:
                        self.logmsg(
                            f"DUAL-BAND watcher GUI: fine CATTURA, controllo {bssid} ch {ch}"
                        )
                    except Exception:
                        pass
                    # La PASSIVA viene gestita dal flusso ordinato
                    # BANDE -> CASCATA soltanto dopo l'analisi finale del segmento.
                    # Il watcher non apre più popup autonomi.

        except Exception as e:
            try:
                self.command_debug_write(f"[DUAL-BAND] Errore watcher GUI: {e}")
            except Exception:
                pass
            try:
                self.logmsg(f"DUAL-BAND watcher GUI errore: {e}")
            except Exception:
                pass
        finally:
            try:
                self.root.after(300, self._dual_band_completion_watcher)
            except Exception:
                pass


    def _dual_band_value(self,value):
        try:
            if hasattr(value,"get"):
                return str(value.get() or "").strip()
        except Exception:
            pass
        return str(value or "").strip()

    def _dual_band_scan_key(self, bssid, channel):
        """Chiave stabile della singola radio/BSSID analizzata."""
        b = self._dual_band_value(bssid).strip().lower()
        c = self._dual_band_value(channel).strip()
        if not MAC_FULL.match(b):
            return None
        try:
            c = str(int(float(c)))
        except Exception:
            pass
        return (b, c)


    def _dual_band_mark_action_scanned(self, action_kind, bssid, channel):
        """Memorizza che quella radio è già stata analizzata con quell'azione."""
        action = str(action_kind or "").strip().lower()
        if action not in ("client", "passive"):
            return
        key = self._dual_band_scan_key(bssid, channel)
        if key is None:
            return
        try:
            store = getattr(self, "_dual_band_scanned_actions", None)
            if not isinstance(store, dict):
                store = {"client": set(), "passive": set()}
                self._dual_band_scanned_actions = store
            if not isinstance(store.get(action), set):
                store[action] = set(store.get(action) or [])
            store[action].add(key)
            try:
                self.command_debug_write(
                    f"[DUAL-BAND] MEMORIA {action.upper()}: già analizzato {key[0]} ch {key[1]}"
                )
            except Exception:
                pass
        except Exception:
            pass


    def _dual_band_action_already_scanned(self, action_kind, bssid, channel):
        """True solo se quella radio è già stata analizzata con la stessa azione."""
        action = str(action_kind or "").strip().lower()
        if action not in ("client", "passive"):
            return False
        key = self._dual_band_scan_key(bssid, channel)
        if key is None:
            return False
        try:
            store = getattr(self, "_dual_band_scanned_actions", {}) or {}
            values = store.get(action, set()) or set()
            return key in values
        except Exception:
            return False


    def _find_same_bssid_other_band(self,bssid,current_channel,action_kind=""):
        """Trova la radio sorella 2.4/5 GHz con correlazione BSSID robusta.

        Alcuni router cambiano il bit U/L del primo ottetto fra le due radio
        (es. A4:.. <-> A6:..) e/o aggiungono '5', '5G', '5GHz' all'SSID.
        Il vecchio controllo richiedeva OUI letteralmente identico e quindi
        scartava proprio questi casi.
        """
        import re as _re

        def norm_mac(value):
            m = str(value or "").strip().lower()
            return m if MAC_FULL.match(m) else ""

        def parts(value):
            m = norm_mac(value)
            return m.split(":") if m else []

        def middle4(value):
            p = parts(value)
            return ":".join(p[1:5]) if len(p) == 6 else ""

        def canonical_oui(value):
            """OUI normalizzato ignorando il bit locally-administered (U/L)."""
            p = parts(value)
            if len(p) != 6:
                return ""
            try:
                first = int(p[0], 16) & 0xFD
                return f"{first:02x}:{p[1]}:{p[2]}"
            except Exception:
                return ""

        def last24(value):
            p = parts(value)
            if len(p) != 6:
                return None
            try:
                return int("".join(p[3:6]), 16)
            except Exception:
                return None

        def band_from_ch(value):
            try:
                ch = int(float(str(value).strip()))
            except Exception:
                return ""
            if 1 <= ch <= 14:
                return "2.4"
            if 32 <= ch <= 177:
                return "5"
            return ""

        def ssid_signature(value):
            """Restituisce (radice, suffisso_banda).

            Esempi considerati correlabili:
              CASA <-> CASA5
              CASA <-> CASA5G
              CASA <-> CASA5GHz
              CASA_5G <-> CASA
              CASA-5GHz <-> CASA
            """
            s = str(value or "").strip().casefold()
            if not s:
                return "", ""

            compact = _re.sub(r"[\s_\-\.]+", "", s)

            suffix = ""
            root = compact

            m = _re.match(r"^(.*?)(5ghz|5g|5)$", compact)
            if m and m.group(1):
                root = m.group(1)
                suffix = m.group(2)
            else:
                # Varianti tipiche della radio 2.4 GHz.
                # Dopo la rimozione di spazi/punti/separatori:
                #   "CASA 2.4"     -> "casa24"
                #   "CASA 2.4G"    -> "casa24g"
                #   "CASA 2.4 GHz" -> "casa24ghz"
                m24 = _re.match(r"^(.*?)(24ghz|24g|24|2ghz|2g)$", compact)
                if m24 and m24.group(1):
                    root = m24.group(1)
                    suffix = m24.group(2)

            return root, suffix

        def ssid_root(value):
            return ssid_signature(value)[0]

        bssid = self._dual_band_value(bssid)
        current_channel = self._dual_band_value(current_channel)
        current_bssid = norm_mac(bssid)
        current_band = band_from_ch(current_channel)
        current_middle = middle4(current_bssid)
        current_coui = canonical_oui(current_bssid)

        try:
            self.command_debug_write(
                f"[DUAL-BAND] Controllo robusto: BSSID={current_bssid} "
                f"CH={current_channel} BAND={current_band} "
                f"MIDDLE4={current_middle} COUI={current_coui}"
            )
        except Exception:
            pass

        if not current_bssid or current_band not in ("2.4", "5"):
            return None

        candidates = []
        seen = set()

        def add_row(vals, origin):
            try:
                vals = tuple(vals or ())
                if len(vals) < 2:
                    return
                ob = norm_mac(vals[0])
                oc = str(vals[1]).strip()
                if not ob:
                    return
                key = (ob, oc)
                if key in seen:
                    return
                seen.add(key)
                candidates.append((vals, origin))
            except Exception:
                pass

        try:
            for iid in self.ap_tree.get_children(""):
                add_row(self.ap_tree.item(iid, "values"), "GUI")
        except Exception:
            pass

        try:
            for vals in (getattr(self, "_dual_band_ap_snapshot", {}) or {}).values():
                add_row(vals, "SNAPSHOT")
        except Exception:
            pass

        try:
            hist = self._network_graph_ensure_history()
            for vals in (hist.get("routers", {}) or {}).values():
                add_row(vals, "SESSIONE")
        except Exception:
            pass

        def ap_row_ssid(vals):
            """Estrae l'ESSID dalla riga AP.

            ap_tree usa: BSSID, CH, BANDA, CLIENTI, PACCHETTI, CRIPTAZIONE,
            POTENZA, ESSID. Il vecchio codice usava vals[3] (CLIENTI) e quindi
            la correlazione 2.4/5 GHz poteva fallire anche con entrambe le radio
            presenti. Per compatibilità con snapshot/righe legacy preferiamo
            l'indice 7 e, se assente, l'ultima colonna testuale disponibile.
            """
            try:
                vals = tuple(vals or ())
                if len(vals) > 7:
                    return str(vals[7] or "").strip()
                if vals:
                    return str(vals[-1] or "").strip()
            except Exception:
                pass
            return ""

        current_ssid = ""
        for vals, _origin in candidates:
            try:
                if norm_mac(vals[0]) == current_bssid:
                    current_ssid = ap_row_ssid(vals)
                    if current_ssid:
                        break
            except Exception:
                pass
        current_root, current_suffix = ssid_signature(current_ssid)
        try:
            self.command_debug_write(
                f"[DUAL-BAND] ESSID corrente reale: '{current_ssid}' root='{current_root}'"
            )
        except Exception:
            pass

        ranked = []

        for vals, origin in candidates:
            other_bssid = norm_mac(vals[0])
            other_ch = str(vals[1]).strip()
            if not other_bssid or other_bssid == current_bssid:
                continue

            other_band = band_from_ch(other_ch)
            if not other_band or other_band == current_band:
                continue

            # Nella fase ordinata delle bande non fermarsi sul primo BSSID
            # correlato già scannerizzato: saltalo e continua a cercare eventuali
            # altre radio non ancora analizzate per quella specifica azione.
            _action = str(action_kind or "").strip().lower()
            if _action in ("client", "passive"):
                try:
                    if self._dual_band_action_already_scanned(
                        _action, other_bssid, other_ch
                    ):
                        continue
                except Exception:
                    pass

            other_ssid = ap_row_ssid(vals)
            other_root, other_suffix = ssid_signature(other_ssid)

            same_middle4 = bool(current_middle and middle4(other_bssid) == current_middle)
            same_coui = bool(current_coui and canonical_oui(other_bssid) == current_coui)
            exact_ssid = bool(
                current_ssid and other_ssid
                and current_ssid.casefold() == other_ssid.casefold()
            )
            related_ssid = bool(current_root and other_root and current_root == other_root)

            # Correlazione esplicita richiesta per i nomi Wi-Fi:
            # se le due radio sono su bande opposte e i nomi differiscono
            # soltanto per 5 / 5G / 5GHz, la relazione viene proposta
            # anche quando il BSSID non è strutturalmente vicino.
            suffix_5 = {"5", "5g", "5ghz"}
            suffix_24 = {"24", "24g", "24ghz", "2g", "2ghz"}

            current_is_5 = current_suffix in suffix_5
            other_is_5 = other_suffix in suffix_5
            current_is_24 = current_suffix in suffix_24
            other_is_24 = other_suffix in suffix_24

            # Correlazione nominale 5 GHz:
            # CASA <-> CASA5 / CASA5G / CASA5GHz
            ssid_5g_name_match = bool(
                related_ssid
                and current_ssid
                and other_ssid
                and (
                    (current_is_5 and not other_is_5)
                    or (other_is_5 and not current_is_5)
                    or (
                        current_is_5
                        and other_is_5
                        and current_suffix != other_suffix
                    )
                )
            )

            # Correlazione nominale 2.4 GHz:
            # CASA <-> CASA2.4 / CASA2.4G / CASA2.4GHz
            # e anche CASA2.4 <-> CASA5G quando la radice è la stessa.
            ssid_24_name_match = bool(
                related_ssid
                and current_ssid
                and other_ssid
                and (
                    (current_is_24 and not other_is_24)
                    or (other_is_24 and not current_is_24)
                    or (
                        current_is_24
                        and other_is_24
                        and current_suffix != other_suffix
                    )
                )
            )

            ssid_band_name_match = bool(
                ssid_5g_name_match or ssid_24_name_match
            )

            p1 = parts(current_bssid)
            p2 = parts(other_bssid)
            ul_toggle = False
            last_byte_delta = 9999
            try:
                ul_toggle = (
                    len(p1) == 6 and len(p2) == 6
                    and (int(p1[0],16) ^ int(p2[0],16)) in (0x00, 0x02)
                    and p1[1:3] == p2[1:3]
                )
                last_byte_delta = abs(int(p1[5],16) - int(p2[5],16))
            except Exception:
                pass

            l1 = last24(current_bssid)
            l2 = last24(other_bssid)
            low24_delta = abs(l1-l2) if l1 is not None and l2 is not None else 10**9

            strong_family = same_middle4 and same_coui
            family_plus_name = same_middle4 and related_ssid
            oui_name_near = same_coui and related_ssid and low24_delta <= 4096

            # Se entrambe le radio sono già state realmente analizzate con
            # CATTURA PASSIVA nella sessione, questa è un'evidenza aggiuntiva
            # molto forte per lo scanner CLIENT. In particolare evita che la
            # seconda banda venga persa quando i BSSID non sono numericamente
            # vicini ma l'SSID è uguale/correlato. Le memorie CLIENT e PASSIVA
            # restano comunque separate: una cattura passiva NON marca la radio
            # come già scannerizzata CLIENT.
            passive_pair_confirmed = False
            try:
                passive_pair_confirmed = bool(
                    self._dual_band_action_already_scanned(
                        "passive", current_bssid, current_channel
                    )
                    and self._dual_band_action_already_scanned(
                        "passive", other_bssid, other_ch
                    )
                )
            except Exception:
                passive_pair_confirmed = False

            passive_pair_name_match = bool(
                passive_pair_confirmed and (exact_ssid or related_ssid)
            )

            # Il solo nome è sufficiente per PROPORRE una correlazione
            # (non per dichiararla certa) se la differenza è esclusivamente
            # un suffisso tipico di banda:
            # 5 / 5G / 5GHz oppure 2.4 / 2.4G / 2.4GHz.
            name_only_band_proposal = ssid_band_name_match

            if not (
                strong_family
                or family_plus_name
                or oui_name_near
                or name_only_band_proposal
                or passive_pair_name_match
            ):
                try:
                    self.command_debug_write(
                        f"[DUAL-BAND] SCARTATO {other_bssid} ch={other_ch} "
                        f"origin={origin} middle4={same_middle4} coui={same_coui} "
                        f"ssid={related_ssid} ssid5g={ssid_5g_name_match} ssid24={ssid_24_name_match} "
                        f"passive_pair={passive_pair_confirmed} passive_name={passive_pair_name_match} "
                        f"low24_delta={low24_delta}"
                    )
                except Exception:
                    pass
                continue

            score = 0
            reasons = []
            if same_middle4:
                score += 55
                reasons.append("4 byte centrali uguali")
            if same_coui:
                score += 25
                reasons.append("OUI normalizzato uguale")
            if related_ssid:
                score += 20
                reasons.append("SSID correlato")
            if ssid_5g_name_match:
                score += 45
                reasons.append("nomi Wi-Fi differiscono solo per 5/5G/5GHz")
            if ssid_24_name_match:
                score += 45
                reasons.append("nomi Wi-Fi differiscono solo per 2.4/2.4G/2.4GHz")
            if exact_ssid:
                score += 8
                reasons.append("SSID identico")
            if passive_pair_name_match:
                score += 60
                reasons.append(
                    "entrambe le radio già osservate in cattura passiva"
                    if getattr(self, "language", "it") != "en"
                    else "both radios already observed in passive capture"
                )
            if ul_toggle:
                score += 10
                reasons.append("bit U/L compatibile")
            if last_byte_delta <= 32:
                score += 8
                reasons.append("ultimo byte vicino")
            if origin == "GUI":
                score += 3

            best = {
                "bssid": other_bssid,
                "channel": other_ch,
                "band": other_band,
                "prefix": current_middle,
                "score": score,
                "reasons": reasons,
                "ssid": other_ssid,
                "origin": origin,
            }
            ranked.append((score, best))

            try:
                self.command_debug_write(
                    f"[DUAL-BAND] CANDIDATO VALIDO {other_bssid} ch={other_ch} "
                    f"score={score} origin={origin} "
                    f"motivi={'; '.join(reasons)}"
                )
            except Exception:
                pass

        if not ranked:
            try:
                self.command_debug_write(
                    f"[DUAL-BAND] NON TROVATO: {current_bssid} ch={current_channel}; "
                    f"candidati esaminati={len(candidates)}"
                )
            except Exception:
                pass
            return None

        ranked.sort(key=lambda x: x[0], reverse=True)
        best_score, best = ranked[0]

        try:
            self.logmsg(
                f"Dual-band BSSID: {current_bssid} ch {current_channel} "
                f"<-> {best['bssid']} ch {best['channel']} "
                f"(score {best_score}, {', '.join(best['reasons'])})"
            )
            self.command_debug_write(
                f"[DUAL-BAND] TROVATO: {current_bssid} ch {current_channel} "
                f"<-> {best['bssid']} ch {best['channel']} score={best_score}"
            )
        except Exception:
            pass

        return best

    def _dual_band_check_after_client_stop(self,bssid,current_channel):
        """Controllo dual-band esplicito dopo STOP manuale della scansione CLIENT."""
        b=self._dual_band_value(bssid)
        c=self._dual_band_value(current_channel)

        if not MAC_FULL.match(str(b or "").lower()) or not str(c or "").strip():
            try:
                b,c=getattr(self,"_dual_band_last_target",("",""))
                b=self._dual_band_value(b)
                c=self._dual_band_value(c)
            except Exception:
                b,c="",""

        try:
            self.command_debug_write(
                f"[DUAL-BAND] STOP CLIENT: controllo forzato BSSID={b} CH={c}"
            )
        except Exception:
            pass

        if not MAC_FULL.match(str(b or "").lower()) or not str(c or "").strip():
            try:
                self.command_debug_write(
                    "[DUAL-BAND] STOP CLIENT: target non valido, avviso non eseguibile"
                )
            except Exception:
                pass
            return

        try:
            self._show_same_bssid_other_band_warning(b,c, "client")
        except Exception as e:
            try:
                self.command_debug_write(
                    f"[DUAL-BAND] STOP CLIENT: errore controllo: {type(e).__name__}: {e}"
                )
            except Exception:
                pass


    def _dual_band_check_after_manual_stop(self,bssid,current_channel):
        """Compatibilità: il flusso PASSIVO viene gestito dopo l'analisi finale.

        Nessun popup dual-band viene aperto direttamente dallo STOP, per evitare
        che la correlazione di banda e quella di cascata partano in parallelo.
        """
        try:
            self.command_debug_write(
                "[PASSIVE-FLOW] STOP: attendo analisi finale BANDE -> CASCATA."
            )
        except Exception:
            pass
        return False


    def _schedule_dual_band_warning_check(self,bssid,current_channel):
        """Compatibilità legacy.

        La PASSIVA non apre più il popup da timer/retry: l'ordine è gestito
        esclusivamente da _passive_post_scan_workflow dopo l'analisi finale.
        """
        return


    def _passive_router_stage_reset(self, bssid=""):
        """Apre un nuovo livello logico di router per la cattura PASSIVA.

        Tutte le radio 2.4/5 GHz correlate dello stesso router appartengono allo
        stesso livello. Solo quando le correlazioni di banda sono terminate si
        passa alla ricerca del router successivo in cascata.
        """
        self._passive_router_stage_lan_rows = {}
        self._passive_router_stage_bssids = set()
        self._passive_router_stage_caps = []
        self._passive_router_stage_root = str(bssid or "").strip().lower()
        self._passive_workflow_busy = False
        try:
            if MAC_FULL.match(self._passive_router_stage_root):
                self._passive_router_stage_bssids.add(
                    self._passive_router_stage_root
                )
        except Exception:
            pass


    def _passive_router_stage_accumulate(self, cap, rows, bssid):
        """Accumula i risultati LAN di tutte le bande dello stesso router."""
        if not isinstance(
            getattr(self, "_passive_router_stage_lan_rows", None), dict
        ):
            self._passive_router_stage_reset(bssid)

        b = str(bssid or "").strip().lower()
        if MAC_FULL.match(b):
            self._passive_router_stage_bssids.add(b)

        try:
            p = str(cap or "")
            if p and p not in self._passive_router_stage_caps:
                self._passive_router_stage_caps.append(p)
        except Exception:
            pass

        for row in rows or []:
            if len(row) < 5:
                continue
            if str(row[2]) != "LAN CANDIDATO":
                continue
            mac = str(row[0] or "").strip().lower()
            if not MAC_FULL.match(mac) or self.is_multicast_or_broadcast(mac):
                continue

            old = self._passive_router_stage_lan_rows.get(mac)
            if old is None:
                self._passive_router_stage_lan_rows[mac] = tuple(row)
                continue

            # Conserva la riga con evidenza LAN più forte.
            try:
                old_score = self._lan_score_from_evidence(
                    old[3] if len(old) > 3 else ""
                )
                new_score = self._lan_score_from_evidence(
                    row[3] if len(row) > 3 else ""
                )
            except Exception:
                old_score = new_score = 0
            if new_score >= old_score:
                self._passive_router_stage_lan_rows[mac] = tuple(row)


    def _passive_post_scan_workflow(self, cap, rows, bssid, channel, run_id=None):
        """Ordine obbligatorio della cattura PASSIVA:

        1. termina tutte le correlazioni di BANDA dello stesso router;
        2. soltanto dopo cerca un ROUTER IN CASCATA;
        3. il router in cascata apre un nuovo livello e riparte dal punto 1.

        In questo modo funziona anche:
        ROUTER -> ROUTER CASCATA -> ROUTER CASCATA -> ...
        """
        bssid = str(bssid or "").strip().lower()
        channel = str(channel or "").strip()

        # Evita di gestire due volte lo stesso segmento per callback tardive.
        if not isinstance(
            getattr(self, "_passive_workflow_handled", None), set
        ):
            self._passive_workflow_handled = set()
        _key = (
            str(run_id if run_id is not None else ""),
            bssid,
            channel,
            str(cap or "")
        )
        if _key in self._passive_workflow_handled:
            return
        self._passive_workflow_handled.add(_key)

        self._passive_router_stage_accumulate(cap, rows, bssid)

        try:
            self.command_debug_write(
                f"[PASSIVE-FLOW] livello router: "
                f"{sorted(self._passive_router_stage_bssids)}"
            )
        except Exception:
            pass

        # FASE 1: BANDE. Se l'utente sceglie SI, parte la nuova cattura
        # correlata e NON deve ancora essere cercata nessuna cascata.
        try:
            band_scan_started = bool(
                self._show_same_bssid_other_band_warning(
                    bssid, channel, "passive"
                )
            )
        except Exception as e:
            band_scan_started = False
            try:
                self.command_debug_write(
                    f"[PASSIVE-FLOW] errore correlazione banda: {e}"
                )
            except Exception:
                pass

        if band_scan_started:
            try:
                self.command_debug_write(
                    "[PASSIVE-FLOW] nuova banda avviata; "
                    "ricerca cascata rinviata."
                )
            except Exception:
                pass
            return

        # FASE 2: tutte le bande accettate sono concluse (oppure l'utente ha
        # scelto NO). Ora usa l'insieme dei risultati del router per cercare
        # il successivo apparato in cascata.
        stage_rows = list(
            (getattr(self, "_passive_router_stage_lan_rows", {}) or {}).values()
        )

        try:
            self.command_debug_write(
                f"[PASSIVE-FLOW] bande terminate; ricerca cascata con "
                f"{len(stage_rows)} LAN unici."
            )
        except Exception:
            pass

        self._cascade_offer_second_scan(
            cap,
            stage_rows,
            stage_bssids=set(
                getattr(self, "_passive_router_stage_bssids", set()) or set()
            )
        )



    def _dual_band_prompt_key(self, action_kind, bssid, current_channel, other):
        """Chiave della singola proposta, separata tra CLIENT e PASSIVA."""
        action = str(action_kind or "").strip().lower()
        src = str(bssid or "").strip().lower()
        dst = str((other or {}).get("bssid", "") or "").strip().lower()
        ch1 = str(current_channel or "").strip()
        ch2 = str((other or {}).get("channel", "") or "").strip()
        try:
            ch1 = str(int(float(ch1)))
        except Exception:
            pass
        try:
            ch2 = str(int(float(ch2)))
        except Exception:
            pass
        return (action, src, ch1, dst, ch2)


    def _dual_band_launch_related_scan(self, other, action_kind):
        """Avvia la scansione scelta dall'utente sul BSSID correlato.

        CLIENT -> nuova scansione CLIENT.
        PASSIVE -> nuova cattura PASSIVA di 120 secondi, nello stesso PCAP di sessione.
        """
        action = str(action_kind or "").strip().lower()
        target_bssid = str((other or {}).get("bssid", "") or "").strip().lower()
        target_ch = str((other or {}).get("channel", "") or "").strip()

        if not MAC_FULL.match(target_bssid) or not target_ch.isdigit():
            messagebox.showwarning(
                "Correlazione BSSID" if getattr(self, "language", "it") != "en"
                else "BSSID correlation",
                "BSSID/canale correlato non valido."
                if getattr(self, "language", "it") != "en"
                else "Invalid correlated BSSID/channel."
            )
            return

        source_bssid = str(self.bssid.get() or "").strip().lower()
        source_ch = str(self.channel.get() or "").strip()

        if action == "client":
            self._client_preserve_previous_for_correlation = True
            self._client_next_relation = "dual_band"
            # Protegge la tabella CLIENT anche dal <<TreeviewSelect>> generato
            # automaticamente quando evidenziamo il BSSID correlato.
            self._client_keep_rows_on_ap_select = True
            try:
                self._network_graph_snapshot_current(
                    source_bssid, "before correlated client scan"
                )
            except Exception:
                pass

        elif action == "passive":
            self._prepare_correlated_passive_preservation(
                source_bssid,
                source_ch,
                target_bssid,
                target_ch,
                "dual_band"
            )

        # Mostra immediatamente nella GUI il nuovo target.
        self.bssid.set(target_bssid)
        self.channel.set(target_ch)
        self.client.set("")
        try:
            self.block_router_value.set(target_bssid)
            self.block_client_value.set("")
        except Exception:
            pass

        try:
            for iid in self.ap_tree.get_children(""):
                vals = self.ap_tree.item(iid, "values") or ()
                if vals and str(vals[0]).strip().lower() == target_bssid:
                    self.ap_tree.selection_set(iid)
                    self.ap_tree.focus(iid)
                    self.ap_tree.see(iid)
                    break
        except Exception:
            pass

        try:
            self._update_capture_panel_titles()
            self._refresh_language_dynamic_texts()
        except Exception:
            pass

        if action == "client":
            self.set_status(
                f"Nuova scansione CLIENT sul BSSID correlato {target_bssid} / canale {target_ch}."
                if getattr(self, "language", "it") != "en"
                else
                f"New CLIENT scan on related BSSID {target_bssid} / channel {target_ch}."
            )
            try:
                self.logmsg(
                    ("CORRELAZIONE DUAL-BAND -> nuova scansione CLIENT: "
                     if getattr(self, "language", "it") != "en"
                     else "DUAL-BAND CORRELATION -> new CLIENT scan: ")
                    + f"{target_bssid} | CH {target_ch}"
                )
            except Exception:
                pass

            # La scansione precedente è già terminata: lascia solo il tempo
            # necessario a Tk per aggiornare BSSID/canale prima di ripartire.
            self.root.after(250, self.scan_clients)
            # Il flag resta attivo abbastanza da coprire gli eventi Tk asincroni
            # prodotti dalla selezione programmatica del router correlato.
            self.root.after(1200, lambda: setattr(self, "_client_keep_rows_on_ap_select", False))
            return

        if action == "passive":
            try:
                self.capture_duration.set(120)
            except Exception:
                pass

            # Solo una scelta SI per la PASSIVA registra la continuazione PCAP.
            try:
                self._capture_chain_register_expected_second_scan(
                    target_bssid, "dual_band"
                )
            except Exception:
                pass

            self.set_status(
                f"Nuova cattura PASSIVA di 120 secondi sul BSSID correlato "
                f"{target_bssid} / canale {target_ch}."
                if getattr(self, "language", "it") != "en"
                else
                f"New 120-second PASSIVE capture on related BSSID "
                f"{target_bssid} / channel {target_ch}."
            )
            try:
                self.logmsg(
                    ("CORRELAZIONE DUAL-BAND -> nuova cattura PASSIVA 120 s: "
                     if getattr(self, "language", "it") != "en"
                     else "DUAL-BAND CORRELATION -> new 120 s PASSIVE capture: ")
                    + f"{target_bssid} | CH {target_ch}"
                )
            except Exception:
                pass

            self.root.after(350, self.start_capture)
            return


    def _askyesno_colored_border(self, title, message, border_color="#1565C0"):
        """
        Popup SI/NO completamente INTERNO alla GUI.

        WIFI_434:
        non usa più tk.Toplevel. Su Kali/Xfce la creazione di una finestra
        transient poteva far perdere temporaneamente il fullscreen alla root
        e rendere visibile il pannello superiore del desktop. Con un Frame
        interno esiste una sola finestra gestita dal window manager, quindi
        la GUI principale resta realmente a tutto schermo per tutta la durata
        del popup.
        """
        result_var = tk.BooleanVar(master=self.root, value=False)
        finished_var = tk.BooleanVar(master=self.root, value=False)

        dark = bool(getattr(self, "night_mode", False))
        bg = "#11161B" if dark else "#F2F2F2"
        fg = "#F2F2F2" if dark else "#111111"

        # Prima di mostrare il pannello, riafferma il fullscreen della root.
        try:
            self.root.deiconify()
            self.root.attributes("-fullscreen", True)
            self.root.lift()
            self.root.update_idletasks()
            self.root.update()
        except Exception:
            pass

        # Contenitore interno: nessuna nuova finestra viene comunicata a XFCE.
        popup = tk.Frame(
            self.root,
            bg=border_color,
            bd=0,
            highlightthickness=0
        )

        outer = tk.Frame(popup, bg=border_color, bd=0, highlightthickness=0)
        outer.pack(fill="both", expand=True)

        body = tk.Frame(outer, bg=bg, bd=0, highlightthickness=0)
        body.pack(fill="both", expand=True, padx=12, pady=12)

        # Barra titolo interna, al posto della titlebar del window manager.
        titlebar = tk.Frame(body, bg=bg, bd=0, highlightthickness=0)
        titlebar.pack(fill="x", padx=12, pady=(8, 0))

        tk.Label(
            titlebar,
            text=title,
            bg=bg,
            fg=fg,
            anchor="center",
            justify="center",
            font=("TkDefaultFont", 10, "bold"),
            pady=3
        ).pack(fill="x", expand=True)

        tk.Label(
            body,
            text=message,
            bg=bg,
            fg=fg,
            justify="left",
            anchor="w",
            font=("TkDefaultFont", 10),
            padx=18,
            pady=16
        ).pack(fill="both", expand=True)

        buttons = tk.Frame(body, bg=bg)
        buttons.pack(fill="x", padx=18, pady=(0, 16))

        yes_text = "YES" if getattr(self, "language", "it") == "en" else "SÌ"
        no_text = "NO"

        button_bg = "#2B3137" if dark else "#E6E6E6"
        button_fg = "#F5F5F5" if dark else "#111111"
        button_active_bg = "#3A424A" if dark else "#D0D0D0"
        button_active_fg = "#FFFFFF" if dark else "#000000"

        def choose(value):
            try:
                result_var.set(bool(value))
                finished_var.set(True)
            except Exception:
                pass

        yes_btn = tk.Button(
            buttons,
            text=yes_text,
            command=lambda: choose(True),
            width=11,
            font=("TkDefaultFont", 10, "bold"),
            cursor="hand2",
            bg=button_bg,
            fg=button_fg,
            activebackground=button_active_bg,
            activeforeground=button_active_fg,
            relief="raised",
            borderwidth=2
        )
        yes_btn.pack(side="right", padx=(8, 0))

        no_btn = tk.Button(
            buttons,
            text=no_text,
            command=lambda: choose(False),
            width=11,
            font=("TkDefaultFont", 10, "bold"),
            cursor="hand2",
            bg=button_bg,
            fg=button_fg,
            activebackground=button_active_bg,
            activeforeground=button_active_fg,
            relief="raised",
            borderwidth=2
        )
        no_btn.pack(side="right")

        # Calcola le dimensioni reali e centra il popup DENTRO la root.
        popup.update_idletasks()
        req_w = max(560, min(900, int(popup.winfo_reqwidth())))
        req_h = max(260, min(650, int(popup.winfo_reqheight())))

        try:
            self.root.update_idletasks()
            rw = max(800, int(self.root.winfo_width()))
            rh = max(600, int(self.root.winfo_height()))
        except Exception:
            rw = max(800, int(self.root.winfo_screenwidth()))
            rh = max(600, int(self.root.winfo_screenheight()))

        req_w = min(req_w, max(520, rw - 30))
        req_h = min(req_h, max(240, rh - 30))
        x = max(0, (rw - req_w) // 2)
        y = max(0, (rh - req_h) // 2)

        popup.place(x=x, y=y, width=req_w, height=req_h)
        popup.lift()

        # Grab sul Frame interno: interazione modale senza creare Toplevel.
        try:
            popup.grab_set()
        except Exception:
            pass

        # Impedisce che ESC faccia uscire la finestra principale dal fullscreen
        # mentre il popup è attivo.
        esc_bind_id = None
        try:
            esc_bind_id = self.root.bind("<Escape>", lambda _e: (choose(False), "break")[1], add="+")
        except Exception:
            pass

        try:
            no_btn.focus_force()
        except Exception:
            pass

        # Attende la scelta continuando a processare l'event loop Tk.
        try:
            self.root.wait_variable(finished_var)
        finally:
            try:
                popup.grab_release()
            except Exception:
                pass
            try:
                popup.destroy()
            except Exception:
                pass
            # Ripristina il binding ESC standard del programma.
            try:
                if esc_bind_id:
                    self.root.unbind("<Escape>", esc_bind_id)
            except Exception:
                pass
            try:
                self.root.attributes("-fullscreen", True)
                self.root.lift()
                self.root.focus_force()
                self.root.update_idletasks()
            except Exception:
                pass

        return bool(result_var.get())

    def _show_same_bssid_other_band_warning(self,bssid,current_channel,action_kind=""):
        """Propone SI/NO senza countdown.

        Le decisioni CLIENT e PASSIVA sono completamente separate:
        - dopo una scansione CLIENT, SI avvia un'altra scansione CLIENT;
        - dopo una cattura PASSIVA, SI avvia un'altra cattura PASSIVA;
        - NO chiude quella specifica proposta e non la ripresenta nella sessione.
        """
        action = str(action_kind or "").strip().lower()
        if action not in ("client", "passive"):
            return False

        try:
            self.command_debug_write(
                f"[DUAL-BAND] Richiesta proposta SI/NO: {bssid} ch {current_channel} "
                f"azione={action}"
            )
        except Exception:
            pass

        other = self._find_same_bssid_other_band(bssid, current_channel, action)
        if not other:
            try:
                self.command_debug_write(
                    "[DUAL-BAND] Nessuna proposta: radio correlata non trovata."
                )
            except Exception:
                pass
            return False

        other_bssid = str(other.get("bssid", "") or "").strip().lower()
        other_channel = str(other.get("channel", "") or "").strip()

        # Se quella stessa radio è già stata analizzata con la stessa azione,
        # non deve essere riproposta.
        if self._dual_band_action_already_scanned(
            action, other_bssid, other_channel
        ):
            try:
                label = "CLIENT" if action == "client" else "PASSIVA"
                self.command_debug_write(
                    f"[DUAL-BAND] PROPOSTA SOPPRESSA: {other_bssid} ch {other_channel} "
                    f"già analizzato come {label}."
                )
            except Exception:
                pass
            return False

        # I retry temporizzati dello STOP/manuale non devono aprire più volte
        # la stessa domanda dopo che l'utente ha già scelto SI oppure NO.
        pkey = self._dual_band_prompt_key(
            action, bssid, current_channel, other
        )
        try:
            decisions = getattr(self, "_dual_band_prompt_decisions", None)
            if not isinstance(decisions, dict):
                decisions = {"client": set(), "passive": set()}
                self._dual_band_prompt_decisions = decisions
            if not isinstance(decisions.get(action), set):
                decisions[action] = set(decisions.get(action) or [])
            if pkey in decisions[action]:
                try:
                    self.command_debug_write(
                        f"[DUAL-BAND] PROPOSTA GIÀ GESTITA: azione={action} "
                        f"{bssid} -> {other_bssid}"
                    )
                except Exception:
                    pass
                return False
        except Exception:
            decisions = {"client": set(), "passive": set()}
            self._dual_band_prompt_decisions = decisions

        # La correlazione è un'informazione trovata e viene comunque conservata
        # nello schema; la nuova scansione parte invece SOLO dopo scelta SI.
        try:
            self._network_graph_snapshot_current(
                bssid,
                "dual-band client correlation"
                if action == "client"
                else "dual-band passive correlation"
            )
            self._network_graph_register_dual_band(
                bssid, other_bssid
            )
        except Exception:
            pass

        en = getattr(self, "language", "it") == "en"
        try:
            cur_band = (
                "2.4"
                if 1 <= int(float(str(current_channel))) <= 14
                else "5"
            )
        except Exception:
            cur_band = "?"

        target_band = str(other.get("band", "") or "")
        if not target_band:
            try:
                target_band = (
                    "2.4"
                    if 1 <= int(float(other_channel)) <= 14
                    else "5"
                )
            except Exception:
                target_band = "?"

        # WIFI_432: NOME = vero nome Wi-Fi (ESSID/SSID) del BSSID esatto.
        # Prima si cerca il BSSID nella tabella router, usando la colonna "essid".
        # Solo se non è disponibile si usano le memorie/snapshot di correlazione.
        def _popup_wifi_name_for_bssid(_bssid):
            _b = str(_bssid or "").strip().lower()
            if not _b:
                return ""
            try:
                _cols = list(self.ap_tree["columns"])
                _bi = _cols.index("bssid")
                _ei = _cols.index("essid")
                for _iid in self.ap_tree.get_children(""):
                    _vals = tuple(self.ap_tree.item(_iid, "values") or ())
                    if (
                        len(_vals) > max(_bi, _ei)
                        and str(_vals[_bi] or "").strip().lower() == _b
                    ):
                        _name = str(_vals[_ei] or "").strip()
                        if _name and _name.lower() not in ("<hidden>", "hidden"):
                            return _name
                        return ""
            except Exception:
                pass
            try:
                _name = str(self._ssid_for_scan_source(_b) or "").strip()
                if _name and _name.lower() not in ("<hidden>", "hidden"):
                    return _name
            except Exception:
                pass
            return ""

        current_name = _popup_wifi_name_for_bssid(bssid)
        target_name = _popup_wifi_name_for_bssid(other_bssid)

        # Ultimo fallback esclusivamente per il BSSID proposto: valore SSID
        # già prodotto dal correlatore, purché non sembri un valore di sicurezza.
        if not target_name:
            try:
                _candidate_name = str(other.get("ssid", "") or "").strip()
                _security_words = {
                    "wpa", "wpa2", "wpa3", "wep", "opn", "open",
                    "wpa2 wpa3", "wpa/wpa2", "wpa2/wpa3"
                }
                if _candidate_name.lower() not in _security_words:
                    target_name = _candidate_name
            except Exception:
                pass

        reasons = ", ".join(other.get("reasons", []) or [])
        score = other.get("score", "")

        if action == "client":
            if en:
                title = "RELATED BSSID - CLIENT SCAN"
                msg = (
                    "A BSSID that may belong to the same router was detected "
                    "on another frequency.\n\n"
                    f"CURRENT BSSID - ALREADY SCANNED:\n"
                    f"    NAME: {current_name or 'UNKNOWN'}\n"
                    f"    {str(bssid).upper()}    {cur_band}GHz    CH {current_channel}\n\n"
                    f"NEW BSSID - TO BE SCANNED:\n"
                    f"    NAME: {target_name or 'UNKNOWN'}\n"
                    f"    {other_bssid.upper()}    {target_band}GHz    CH {other_channel}\n"
                    + (f"Correlation: {score}/100\n" if score != "" else "")
                    + (f"Evidence: {reasons}\n" if reasons else "")
                    + "\nRun a new CLIENT scan on the proposed BSSID?"
                )
            else:
                title = "BSSID CORRELATO - SCANSIONE CLIENT"
                msg = (
                    "È stato rilevato un BSSID che potrebbe appartenere allo stesso "
                    "router su un'altra frequenza.\n\n"
                    f"BSSID ATTUALE - GIÀ SCANSIONATO:\n"
                    f"    NOME: {current_name or 'SCONOSCIUTO'}\n"
                    f"    {str(bssid).upper()}    {cur_band}GHz    CH {current_channel}\n\n"
                    f"NUOVO BSSID - DA SCANSIONARE:\n"
                    f"    NOME: {target_name or 'SCONOSCIUTO'}\n"
                    f"    {other_bssid.upper()}    {target_band}GHz    CH {other_channel}\n"
                    + (f"Correlazione: {score}/100\n" if score != "" else "")
                    + (f"Indizi: {reasons}\n" if reasons else "")
                    + "\nEseguire una nuova SCANSIONE CLIENT sul BSSID proposto?"
                )
        else:
            if en:
                title = "RELATED BSSID - PASSIVE CAPTURE"
                msg = (
                    "A BSSID that may belong to the same router was detected "
                    "on another frequency.\n\n"
                    f"CURRENT BSSID - ALREADY SCANNED:\n"
                    f"    NAME: {current_name or 'UNKNOWN'}\n"
                    f"    {str(bssid).upper()}    {cur_band}GHz    CH {current_channel}\n\n"
                    f"NEW BSSID - TO BE SCANNED:\n"
                    f"    NAME: {target_name or 'UNKNOWN'}\n"
                    f"    {other_bssid.upper()}    {target_band}GHz    CH {other_channel}\n"
                    + (f"Correlation: {score}/100\n" if score != "" else "")
                    + (f"Evidence: {reasons}\n" if reasons else "")
                    + "\nRun a new 120-second PASSIVE capture on the proposed BSSID?"
                )
            else:
                title = "BSSID CORRELATO - CATTURA PASSIVA"
                msg = (
                    "È stato rilevato un BSSID che potrebbe appartenere allo stesso "
                    "router su un'altra frequenza.\n\n"
                    f"BSSID ATTUALE - GIÀ SCANSIONATO:\n"
                    f"    NOME: {current_name or 'SCONOSCIUTO'}\n"
                    f"    {str(bssid).upper()}    {cur_band}GHz    CH {current_channel}\n\n"
                    f"NUOVO BSSID - DA SCANSIONARE:\n"
                    f"    NOME: {target_name or 'SCONOSCIUTO'}\n"
                    f"    {other_bssid.upper()}    {target_band}GHz    CH {other_channel}\n"
                    + (f"Correlazione: {score}/100\n" if score != "" else "")
                    + (f"Indizi: {reasons}\n" if reasons else "")
                    + "\nEseguire una nuova CATTURA PASSIVA di 120 secondi sul BSSID proposto?"
                )

        # Segna la domanda come gestita PRIMA di aprirla: gli altri callback
        # già pianificati non potranno aprire un secondo popup.
        try:
            self._dual_band_prompt_decisions[action].add(pkey)
        except Exception:
            pass

        # Altra banda wireless / BSSID correlato: cornice BLU.
        choice = self._askyesno_colored_border(title, msg, "#1565C0")

        if not choice:
            try:
                label = "CLIENT" if action == "client" else "PASSIVA"
                self.logmsg(
                    f"Dual-band: scelta NO per {other_bssid} ch {other_channel} "
                    f"({label}); nessuna nuova scansione avviata."
                )
                self.command_debug_write(
                    f"[DUAL-BAND] NO: azione={action} target={other_bssid} "
                    f"ch={other_channel}; procedura terminata."
                )
            except Exception:
                pass
            return False

        try:
            self.command_debug_write(
                f"[DUAL-BAND] SI: azione={action} -> {other_bssid} ch {other_channel}"
            )
        except Exception:
            pass

        self._dual_band_launch_related_scan(other, action)
        return True



    def parse_airodump_csv(self,path,target_bssid=None):
        if target_bssid:
            target_bssid=target_bssid.strip().lower()
        aps=[]
        clients=[]
        section=None
        with open(path,encoding="utf-8",errors="ignore",newline="") as f:
            for row in csv.reader(f):
                if not row:
                    continue
                first=row[0].strip()

                if first=="BSSID":
                    section="ap"
                    continue
                if first=="Station MAC":
                    section="client"
                    continue

                if section=="ap":
                    if len(row)<14:
                        continue
                    bssid=row[0].strip().lower()
                    if not MAC_FULL.match(bssid):
                        continue
                    try:
                        data_packets=int((row[10] or "0").strip() or 0)
                    except Exception:
                        data_packets=0

                    aps.append((
                        bssid,
                        row[3].strip(),
                        row[5].strip(),
                        row[8].strip(),
                        row[13].strip() if row[13].strip() else "<hidden>",
                        data_packets
                    ))

                elif section=="client":
                    if len(row)<6:
                        continue
                    station=row[0].strip().lower()
                    if not MAC_FULL.match(station):
                        continue

                    assoc_bssid=row[5].strip().lower() if len(row)>5 else ""
                    if target_bssid and assoc_bssid.strip().lower() != target_bssid:
                        continue

                    power=row[3].strip() if len(row)>3 else ""
                    packets=row[4].strip() if len(row)>4 else ""
                    probes=row[6].strip() if len(row)>6 else ""

                    clients.append({
                        "station":station,
                        "power":power,
                        "packets":packets,
                        "bssid":assoc_bssid,
                        "probes":probes
                    })

        return aps,clients

    def parse_client_counts_by_bssid(self, csvfile):
        """
        Legge la sezione Station del CSV di airodump-ng e restituisce
        {bssid: set(mac_station)} per tutti gli AP osservati.
        Non richiede una scansione client separata.
        """
        counts = {}
        try:
            raw = Path(csvfile).read_text(encoding="utf-8", errors="ignore")
        except Exception as e:
            self.logmsg(f"Impossibile leggere CSV per conteggio client: {e}")
            return counts

        in_station_section = False

        for line in raw.splitlines():
            # La seconda sezione del CSV inizia con "Station MAC".
            if line.strip().lower().startswith("station mac"):
                in_station_section = True
                continue

            if not in_station_section:
                continue

            if not line.strip():
                continue

            parts = [x.strip() for x in line.split(",")]
            # Formato airodump:
            # Station MAC, First time seen, Last time seen, Power,
            # # packets, BSSID, Probed ESSIDs
            if len(parts) < 6:
                continue

            station = parts[0].lower()
            associated_bssid = parts[5].lower()

            if not MAC_FULL.match(station):
                continue
            if not MAC_FULL.match(associated_bssid):
                # "(not associated)" e simili vengono esclusi.
                continue
            if self.is_multicast_or_broadcast(station):
                continue

            counts.setdefault(associated_bssid, set()).add(station)

        return counts

    def fill_aps(self,aps, client_counts=None):
        for x in self.ap_tree.get_children():
            self.ap_tree.delete(x)

        client_counts = client_counts or {}
        inserted=0

        # Ricostruisce la cache dai risultati correnti di airodump-ng.
        self.ap_client_counts = {}

        # Stesso ordinamento usato durante la scansione live:
        # gruppi ESSID ordinati per segnale migliore, righe del gruppo per PWR.
        aps = self._sort_aps_grouped_pre201(aps)

        for ap in aps:
            try:
                bssid, ch, enc, pwr, essid, packets = ap
                bssid_l=bssid.lower()
                band=self.band_from_channel(ch)

                stations=set(client_counts.get(bssid_l,set()))
                count=len(stations)
                self.ap_client_counts[bssid_l]=count

                _ap_row=(bssid,ch,pwr,essid,band,count,packets,enc)
                self.ap_tree.insert("", "end", values=_ap_row)

                # Mantiene SEMPRE la memoria delle radio viste, anche nel refresh
                # finale che cancella e ricostruisce la Treeview.
                if not hasattr(self, "_dual_band_ap_snapshot"):
                    self._dual_band_ap_snapshot={}
                self._dual_band_ap_snapshot[
                    (str(bssid).lower(),str(ch),str(band))
                ]=tuple(_ap_row)

                inserted += 1
            except Exception as e:
                self.logmsg(f"Errore visualizzazione AP {ap}: {e}")

        try:
            self.root.after(0, self.router_count.set, f"Numero: {inserted}")
        except Exception:
            pass

        if aps and inserted == 0:
            self.set_status("Router rilevati ma non visualizzabili: controlla il log.")

        try:
            self._network_graph_snapshot_current(None, "router scan")
        except Exception:
            pass

    def _load_tshark_manuf_cache(self):
        """
        Carica una volta la tabella OUI/manufacturer locale usata da Wireshark.
        `tshark -G manuf` non invia traffico di rete.
        """
        if self.manuf_oui_cache is not None:
            return self.manuf_oui_cache

        cache={}
        try:
            p=run(["tshark","-G","manuf"], timeout=12)
            if p.returncode == 0:
                for line in p.stdout.splitlines():
                    s=line.strip()
                    if not s or s.startswith("#"):
                        continue
                    parts=s.split("\t")
                    if len(parts) < 2:
                        continue

                    prefix=parts[0].strip().upper()
                    short=parts[1].strip()
                    long_name=parts[2].strip() if len(parts)>2 else ""

                    # Manteniamo soprattutto prefissi /24, i più comuni per OUI.
                    raw=prefix.split("/")[0].replace("-",":")
                    octets=raw.split(":")
                    if len(octets) >= 3:
                        oui=":".join(octets[:3])
                        cache.setdefault(oui,(short,long_name))
        except Exception as e:
            self.logmsg(f"Risoluzione OUI locale non disponibile: {e}")

        self.manuf_oui_cache=cache
        return cache

    def resolve_mac_with_manuf(self, mac):
        """
        Restituisce una risoluzione tipo Wireshark, ad esempio:
            VendorShort_12:34:56
        usando il database manufacturer locale.
        """
        mac=(mac or "").strip().upper()
        if not MAC_FULL.match(mac.lower()):
            return "Sconosciuto"

        cache=self._load_tshark_manuf_cache()
        oui=":".join(mac.split(":")[:3])
        rec=cache.get(oui)

        if not rec:
            # Se non c'è un OUI noto, segnala anche i MAC localmente amministrati.
            try:
                first=int(mac.split(":")[0],16)
                if first & 0x02:
                    return "MAC locale/randomizzato"
            except Exception:
                pass
            return "Sconosciuto"

        short,long_name=rec
        suffix=":".join(mac.split(":")[3:])
        label=short or long_name or "Vendor"
        return f"{label}_{suffix}"

    def fill_clients(self,rows):
        source = str(getattr(self, "_client_current_source_label", "") or "").strip()
        existing = {}
        for item in self.client_tree.get_children():
            vals_old = tuple(self.client_tree.item(item, "values") or ())
            if vals_old:
                existing[(str(vals_old[0]).lower(), str(vals_old[6] if len(vals_old) > 6 else ""))] = item
        for r in rows:
            vals = tuple(r[:6]) + (source,)
            key = (str(vals[0]).lower(), source)
            if key in existing:
                self.client_tree.item(existing[key], values=vals)
            else:
                existing[key] = self.client_tree.insert("","end",values=vals)
        self._sort_client_tree_by_packets()

        # Conteggio cumulativo delle osservazioni conservate per provenienza.
        prefix = "Count: " if getattr(self, "language", "it") == "en" else "Numero: "
        self.client_count.set(prefix + str(len(self.client_tree.get_children())))

        if hasattr(self, "res_tree"):
            current_rows=[]
            for _item in self.res_tree.get_children():
                _vals=self.res_tree.item(_item,"values")
                if len(_vals) >= 5:
                    current_rows.append(tuple(_vals[:5]))
            self.update_probable_lan_vendors(current_rows)
        try:
            self._refresh_camera_block_action()
        except Exception:
            pass
        try:
            self._network_graph_snapshot_current(None, "client scan")
        except Exception:
            pass

    def _update_capture_panel_titles(self):
        """Aggiorna BSSID/CLIENT visualizzati nei titoli CATTURA PASSIVA e DISTURBO."""
        bssid=(self.bssid.get() or "").strip() or "--"
        client=(self.client.get() or "").strip() or "--"

        try:
            self.passive_box_title.set(
                f"CATTURA PASSIVA   BSSID: {bssid}"
            )
            self.disturb_box_title.set(
                f"DISTURBO   BSSID: {bssid} / CLIENT: {client}"
            )
        except Exception:
            pass

    def _aireplay_ng_button_base_colors(self):
        if getattr(self, "night_mode", False):
            return "#111111", "#d6d8dc"
        return "#e7e7e7", "#000000"

    def _start_aireplay_ng_blink(self, which):
        """
        Mantiene lampeggiante AVVIA del BLOCCO per tutta la durata reale
        dell'operazione. Il lampeggio non può più morire per un errore grafico.
        """
        attr_after = (
            "aireplay_ng_router_blink_after"
            if which == "router"
            else "aireplay_ng_client_blink_after"
        )
        attr_phase = (
            "aireplay_ng_router_blink_phase"
            if which == "router"
            else "aireplay_ng_client_blink_phase"
        )
        attr_running = (
            "aireplay_ng_router_blink_running"
            if which == "router"
            else "aireplay_ng_client_blink_running"
        )
        button_name = (
            "aireplay_ng_router_start_button"
            if which == "router"
            else "aireplay_ng_client_start_button"
        )
        process_name = (
            "aireplay_ng_router_process"
            if which == "router"
            else "aireplay_ng_client_process"
        )

        # Cancella solo il timer precedente, senza passare dalla routine di STOP.
        old_aid = getattr(self, attr_after, None)
        if old_aid is not None:
            try:
                self.root.after_cancel(old_aid)
            except Exception:
                pass

        setattr(self, attr_after, None)
        setattr(self, attr_phase, False)
        setattr(self, attr_running, True)

        def tick():
            if not getattr(self, attr_running, False):
                return

            proc = getattr(self, process_name, None)
            btn = getattr(self, button_name, None)

            # Il processo terminato è uno dei soli motivi validi per fermare il blink.
            if proc is None or proc.poll() is not None:
                self._stop_aireplay_ng_blink(which)
                return

            # Se il widget attraversa un ridisegno temporaneo, NON spegnere il ciclo.
            if btn is not None:
                try:
                    exists = bool(btn.winfo_exists())
                except Exception:
                    exists = False

                if exists:
                    phase = not getattr(self, attr_phase, False)
                    setattr(self, attr_phase, phase)

                    base_bg, base_fg = self._aireplay_ng_button_base_colors()
                    _night = bool(getattr(self, "night_mode", False))
                    _blink_red = "#741A1A" if _night else "#FF0000"
                    _blink_fg = "#F3DCDC" if _night else "#FFFFFF"

                    try:
                        btn.configure(
                            bg=(_blink_red if phase else base_bg),
                            fg=(_blink_fg if phase else base_fg),
                            activebackground=_blink_red,
                            activeforeground=_blink_fg,
                        )
                    except Exception:
                        # Prima qui c'era "return": era la causa del lampeggio che
                        # si interrompeva verso fine avanzamento pur col comando attivo.
                        pass

            # Pianifica SEMPRE il tick successivo finché running resta True.
            if getattr(self, attr_running, False):
                try:
                    aid = self.root.after(450, tick)
                    setattr(self, attr_after, aid)
                except Exception:
                    pass

        try:
            aid = self.root.after(0, tick)
            setattr(self, attr_after, aid)
        except Exception:
            pass

    def _stop_aireplay_ng_blink(self, which, restore=True):
        attr_after = (
            "aireplay_ng_router_blink_after"
            if which == "router"
            else "aireplay_ng_client_blink_after"
        )
        attr_phase = (
            "aireplay_ng_router_blink_phase"
            if which == "router"
            else "aireplay_ng_client_blink_phase"
        )
        attr_running = (
            "aireplay_ng_router_blink_running"
            if which == "router"
            else "aireplay_ng_client_blink_running"
        )
        button_name = (
            "aireplay_ng_router_start_button"
            if which == "router"
            else "aireplay_ng_client_start_button"
        )

        setattr(self, attr_running, False)

        aid = getattr(self, attr_after, None)
        if aid is not None:
            try:
                self.root.after_cancel(aid)
            except Exception:
                pass

        setattr(self, attr_after, None)
        setattr(self, attr_phase, False)

        if not restore:
            return

        btn = getattr(self, button_name, None)
        if btn is not None:
            base_bg, base_fg = self._aireplay_ng_button_base_colors()
            try:
                btn.configure(
                    bg=base_bg,
                    fg=base_fg,
                    activebackground=base_bg,
                    activeforeground=base_fg,
                )
            except Exception:
                pass


    def _start_aireplay_ng_block(self, which):
        """
        Avvia un processo esterno aireplay-ng dedicato al riquadro BLOCCO.

        ROB:
            airodump-ng -c 6 -w ROB --bssid <BSSID> --client <CLIENT> <WLAN>

        MAU:
            airodump-ng -c 6 -w ROB --bssid <BSSID> <WLAN>

        Il processo viene avviato in una nuova sessione, così FERMA può inviare
        SIGINT al gruppo processo (equivalente a Ctrl+C).
        """
        bssid = (self.block_router_value.get() or self.bssid.get() or "").strip().lower()
        client = (self.block_client_value.get() or self.client.get() or "").strip().lower()
        iface = (self.active_monitor_iface or self.iface.get() or "").strip()

        if not MAC_FULL.match(bssid):
            messagebox.showwarning(
                "BLOCCO",
                "Seleziona prima un router/BSSID valido."
            )
            return

        if not iface:
            messagebox.showwarning(
                "BLOCCO",
                "Seleziona prima una interfaccia WLAN valida."
            )
            return

        # Usa SEMPRE il canale associato al BSSID selezionato.
        # Se il campo canale non è aggiornato, lo recupera dalla riga del BSSID.
        ch = (self.channel.get() or "").strip()
        try:
            for _item in self.ap_tree.get_children():
                _vals = self.ap_tree.item(_item, "values")
                if _vals and str(_vals[0]).strip().lower() == bssid:
                    _bssid_ch = str(_vals[1]).strip()
                    if _bssid_ch:
                        ch = _bssid_ch
                        self.channel.set(_bssid_ch)
                    break
        except Exception:
            pass

        if not ch.isdigit():
            messagebox.showwarning(
                "CHANNEL" if getattr(self, "language", "it") == "en" else "CANALE",
                ("Unable to determine the channel of the selected BSSID."
                 if getattr(self, "language", "it") == "en"
                 else "Impossibile determinare il canale del BSSID selezionato.")
            )
            return

        try:
            r_ch = run(["iw", "dev", iface, "set", "channel", ch], timeout=5)
            if getattr(r_ch, "returncode", 0) != 0:
                raise RuntimeError((getattr(r_ch, "stderr", "") or "").strip())
            self.command_debug_write("BLOCCO", f"BSSID {bssid} | canale {ch} | interfaccia {iface}")
        except Exception as e:
            messagebox.showerror(
                "CHANNEL" if getattr(self, "language", "it") == "en" else "CANALE",
                (f"Unable to set BSSID channel {ch} on {iface}:\n{e}"
                 if getattr(self, "language", "it") == "en"
                 else f"Impossibile impostare il canale {ch} del BSSID su {iface}:\n{e}")
            )
            return

        if which == "router":
            process_name = "aireplay_ng_router_process"
            button_name = "aireplay_ng_router_start_button"
            cmd = [
                "aireplay-ng",
                "-0", "0",
                "-a", bssid,
                iface
            ]
            label = "ROB"
        else:
            if not MAC_FULL.match(client):
                messagebox.showwarning(
                    "BLOCCO CLIENT",
                    "Seleziona prima un CLIENT/MAC valido."
                )
                return
            process_name = "aireplay_ng_client_process"
            button_name = "aireplay_ng_client_start_button"
            cmd = [
                "aireplay-ng",
                "-0", "0",
                "-a", bssid,
                "-c", client,
                iface
            ]
            label = "MAU"

        current = getattr(self, process_name, None)
        if current is not None and current.poll() is None:
            self.set_status(f"{label} è già in esecuzione.")
            return

        if shutil.which("aireplay-ng") is None:
            messagebox.showerror(
                label,
                "Comando aireplay-ng non trovato nel PATH."
            )
            return

        self.logmsg("$ " + " ".join(cmd))
        self.command_debug_write("BLOCCO", "$ " + " ".join(cmd))

        try:
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
        except Exception as e:
            messagebox.showerror(
                label,
                f"Errore avvio comando:\n{' '.join(cmd)}\n\n{e}"
            )
            self.command_debug_write("BLOCCO", f"ERRORE AVVIO: {e}")
            return

        setattr(self, process_name, proc)
        self._set_operation_mode_banner("active")
        self.set_status(f"{label} avviato.")
        self.command_debug_write(
            "BLOCCO",
            f"{label} avviato | PID={proc.pid}"
        )
        self._start_aireplay_ng_blink(which)

        def output_reader():
            try:
                if proc.stdout:
                    for line in iter(proc.stdout.readline, ""):
                        if not line:
                            break
                        clean = line.rstrip()
                        if clean:
                            self.logmsg(f"{label}: {clean}")
                            self.command_debug_write(label, clean)
            except Exception as e:
                self.command_debug_write(label, f"ERRORE OUTPUT: {e}")

        threading.Thread(target=output_reader, daemon=True).start()

        def watcher():
            try:
                code = proc.wait()
            except Exception:
                code = "?"

            def done():
                if getattr(self, process_name, None) is proc:
                    setattr(self, process_name, None)
                self._stop_aireplay_ng_blink(which)
                self.set_status(f"{label} terminato (exit={code}).")
                self.command_debug_write(
                    label,
                    f"Processo terminato | exit={code}"
                )
                self._set_operation_mode_banner("idle")

            self.root.after(0, done)

        threading.Thread(target=watcher, daemon=True).start()

    def _stop_aireplay_ng_block(self, which):
        """
        FERMA invia SIGINT al gruppo processo, equivalente a Ctrl+C.
        Se il processo non è attivo, ripristina semplicemente il pulsante.
        """
        process_name = (
            "aireplay_ng_router_process"
            if which == "router"
            else "aireplay_ng_client_process"
        )
        label = "BLOCCO ROUTER" if which == "router" else "BLOCCO CLIENT"

        proc = getattr(self, process_name, None)

        if proc is None or proc.poll() is not None:
            setattr(self, process_name, None)
            self._stop_aireplay_ng_blink(which)
            self.set_status(f"{label} non è in esecuzione.")
            self._set_operation_mode_banner("idle")
            return

        try:
            os.killpg(proc.pid, signal.SIGINT)
            self.set_status(f"Ctrl+C inviato a {label}.")
            self.command_debug_write(
                label,
                f"SIGINT/Ctrl+C inviato al gruppo PID={proc.pid}"
            )
            self._set_operation_mode_banner("idle")
        except Exception:
            try:
                proc.send_signal(signal.SIGINT)
                self.set_status(f"Ctrl+C inviato a {label}.")
                self._set_operation_mode_banner("idle")
            except Exception as e:
                self.logmsg(f"Errore arresto {label}: {e}")
                self.command_debug_write(label, f"ERRORE STOP: {e}")

    def start_aireplay_ng_router(self):
        self._start_aireplay_ng_block("router")

    def stop_aireplay_ng_router(self):
        self._stop_aireplay_ng_block("router")

    def start_aireplay_ng_client(self):
        self._start_aireplay_ng_block("client")

    def stop_aireplay_ng_client(self):
        self._stop_aireplay_ng_block("client")


    def _sort_client_tree_by_packets(self):
        """Ordina i client Wi-Fi per frame/pacchetti osservati, dal maggiore al minore."""
        try:
            cols=list(self.client_tree["columns"])
            if "packets" not in cols:
                return
            packet_idx=cols.index("packets")

            rows=[]
            for item in self.client_tree.get_children():
                vals=self.client_tree.item(item,"values")
                raw=vals[packet_idx] if len(vals)>packet_idx else 0
                try:
                    count=int(str(raw).replace(".","").replace(",","").strip())
                except Exception:
                    try:
                        count=int(float(str(raw).strip()))
                    except Exception:
                        count=0

                # MAC/station come secondo criterio stabile.
                station=str(vals[0]).lower() if vals else ""
                rows.append((item,count,station))

            for pos,(item,_count,_station) in enumerate(
                sorted(rows,key=lambda x:(-x[1],x[2]))
            ):
                self.client_tree.move(item,"",pos)
        except Exception:
            pass

    def on_ap_select(self,_=None):
        sel=self.ap_tree.selection()
        if not sel:
            return
        vals=self.ap_tree.item(sel[0],"values")
        if vals:
            self.bssid.set(vals[0])
            self.channel.set(vals[1])
            self.client.set("")

            # Aggiorna i campi del riquadro BLOCCO.
            try:
                self.block_router_value.set(str(vals[0]))
                self.block_client_value.set("")
            except Exception:
                pass

            try:
                self._update_capture_panel_titles()
            except Exception:
                pass
            self._refresh_language_dynamic_texts()

            try:
                essid = str(vals[3]).strip() if len(vals) > 3 else ""
            except Exception:
                essid = ""
            if not essid:
                essid = "<hidden SSID>" if self.language == "en" else "<SSID nascosto>"

            try:
                if self.language == "en":
                    self.client_search_caption.set(
                        f"Scan clients associated with: {essid} ({vals[0]})"
                    )
                else:
                    self.client_search_caption.set(
                        f"Ricerca Client Associati a: {essid} ({vals[0]})"
                    )
            except Exception:
                pass

            # Se la selezione del router è stata generata dalla proposta
            # dual-band, NON cancellare i risultati CLIENT della prima scansione.
            # L'evento <<TreeviewSelect>> può arrivare in modo asincrono dopo
            # selection_set(), quindi usiamo anche un flag dedicato temporaneo.
            _keep_client_rows = bool(
                getattr(self, "_client_preserve_previous_for_correlation", False)
                or getattr(self, "_client_keep_rows_on_ap_select", False)
            )
            if not _keep_client_rows:
                try:
                    for x in self.client_tree.get_children():
                        self.client_tree.delete(x)
                except Exception:
                    pass

            try:
                known_count = int(vals[5])
            except Exception:
                known_count = self.ap_client_counts.get(str(vals[0]).lower(), 0)

            if self.language == "en":
                self.set_status(
                    f"Selected access point: {vals[0]} - signal {vals[2]} - associated clients observed: {known_count}"
                )
            else:
                self.set_status(
                    f"Router selezionato: {vals[0]} - segnale {vals[2]} - client associati osservati: {known_count}"
                )

    def on_client_select(self,_=None):
        sel=self.client_tree.selection()
        if not sel:
            return
        vals=self.client_tree.item(sel[0],"values")
        if vals:
            self.client.set(vals[0])

            try:
                self.block_client_value.set(str(vals[0]))
            except Exception:
                pass

            try:
                self._update_capture_panel_titles()
            except Exception:
                pass
            self._refresh_language_dynamic_texts()

    def open_diegi_debug(self):
        """Finestra DEBUG DIEGO disabilitata: non viene più visualizzata."""
        return

    def diegi_debug_write(self, message):
        """Output DEBUG DIEGO disabilitato."""
        return

    def _clear_capture_results_on_start(self):
        try:
            self._refresh_camera_block_action()
        except Exception:
            pass

        # Seconda scansione router-cascata:
        # PRESERVA le righe gia' visibili della prima scansione, ma AZZERA
        # lo stato analitico della sessione precedente. Questo e' fondamentale:
        # la seconda cattura deve comportarsi come una vera nuova scansione sul
        # BSSID correlato. In precedenza il return qui sotto manteneva anche
        # wifi_radio_macs_session / live_mac_rows / history LAN della prima
        # cattura e poteva quindi impedire alla camera di essere classificata
        # esattamente come accade in una scansione avviata manualmente.
        if (
            getattr(self, "_preserve_results_for_cascade_scan", False)
            or getattr(self, "_preserve_results_for_correlated_passive_scan", False)
        ):
            self._preserve_results_for_cascade_scan = False
            self._preserve_results_for_correlated_passive_scan = False

            # Le Treeview NON vengono svuotate: i risultati della prima
            # scansione restano visibili e verranno integrati con la seconda.
            # Le copie _cascade_first_* sono state create prima di entrare qui.
            try:
                self.live_mac_rows = {}
                self.lan_seen_rows = {}
                self.lan_candidate_details = {}

                # Nuova sessione LAN reale: nessuna storia/score della prima
                # cattura deve influenzare il BSSID TP-Link.
                self.lan_persistent_rows = {}
                self.lan_persistent_details = {}
                self.lan_candidate_confirmations = {}
                self.lan_low_traffic_history = {}
                self.lan_confirmed_visible = set()

                # CRITICO per telecamere Wi-Fi:
                # le prove radio della prima cattura Netgear non devono essere
                # riutilizzate nella seconda cattura TP-Link.
                self.wifi_radio_macs_session = set()

                # CRITICO: anche le cache CAMERA devono ripartire da zero.
                # La Treeview rimane visibile, ma dal punto di vista analitico
                # questa seconda cattura deve essere uguale a una scansione
                # manuale separata sul BSSID TP-Link.
                self.camera_candidate_rows = {}
                self.camera_candidate_details = {}

                self.live_mac_check_running = False
                self._camera_live_next_at = 0.0
            except Exception:
                pass

            # Manteniamo camera_candidate_rows e camera_candidate_details della
            # prima scansione solo come memoria VISIVA. _merge_camera_candidate_rows
            # aggiungera'/aggiornera' i candidati rilevati nella seconda.
            try:
                self._refresh_lan_score_font_overlay()
                self._refresh_camera_block_action()
                self._refresh_result_counters()
            except Exception:
                pass

            self.logmsg(
                "Seconda scansione cascata: mantenuti i risultati visibili della "
                "prima scansione, azzerato lo stato analitico per il nuovo BSSID."
            )
            return
        try:
            self._refresh_camera_block_action()
        except Exception:
            pass

        # Nuova prima scansione: nessun residuo del precedente ciclo cascata
        # deve poter eliminare il placeholder appena rilevato.
        self._cascade_router_cam_integration_active = False
        self._cascade_router_cam_finalize_merge = False
        self._cascade_router_cam_placeholders = set()

        """
        Pulisce SOLO i risultati derivati dalla cattura:
        - DISPOSITIVI LAN
        - MACS CATTURATI
        - POSSIBILI TELECAMERE RILEVATE

        Viene chiamata una sola volta quando parte realmente AVVIA CATTURA
        oppure AVVIA DISTURBO. Router e client Wi-Fi rilevati restano invariati.
        """
        try:
            for item in self.lan_vendor_tree.get_children():
                self.lan_vendor_tree.delete(item)
        except Exception:
            pass

        try:
            for item in self.res_tree.get_children():
                self.res_tree.delete(item)
        except Exception:
            pass

        try:
            for item in self.camera_tree.get_children():
                self.camera_tree.delete(item)
        except Exception:
            pass
        try:
            self._refresh_result_counters()
        except Exception:
            pass

        try:
            self.probable_lan_vendor_count.set("Numero: 0")
        except Exception:
            pass

        try:
            self.lan_count.set("LAN candidati: 0")
            self.other_count.set("Altro/incerto: 0")
        except Exception:
            pass

        # Azzera anche gli overlay grafici dello SCORE LAN.
        # I tk.Label dell'overlay sono separati dalle righe Treeview: cancellare
        # soltanto la tabella lasciava visibile il vecchio score al nuovo AVVIA.
        try:
            _score_overlays = getattr(self, "_lan_score_overlay_labels", {})
            if isinstance(_score_overlays, dict):
                for _lbl in list(_score_overlays.values()):
                    try:
                        _lbl.destroy()
                    except Exception:
                        pass
                _score_overlays.clear()
            else:
                for _lbl in list(_score_overlays or []):
                    try:
                        _lbl.destroy()
                    except Exception:
                        pass
                self._lan_score_overlay_labels = {}
            self._lan_score_overlay_geometry = {}
            self._lan_score_overlay_state = {}
        except Exception:
            self._lan_score_overlay_labels = {}
            self._lan_score_overlay_geometry = {}
            self._lan_score_overlay_state = {}

        try:
            self.live_mac_rows = {}
            self.lan_seen_rows = {}
            self.lan_candidate_details = {}
            self.camera_candidate_rows = {}
            self.lan_seen_rows = {}
            # I dispositivi LAN restano visibili per tutta la sessione corrente.
            # La memoria viene azzerata soltanto all'avvio di una NUOVA cattura.
            self.lan_persistent_rows = {}
            self.lan_persistent_details = {}
            self.wifi_radio_macs_session = set()
            self.lan_candidate_confirmations = {}
            self.lan_low_traffic_history = {}
            self.lan_confirmed_visible = set()
            self.live_mac_check_running = False
            self._camera_live_next_at = 0.0
        except Exception:
            pass

        try:
            self._refresh_lan_score_font_overlay()
        except Exception:
            pass

        self.logmsg(
            "Avvio nuova sessione: cancellati DISPOSITIVI LAN, MACS CATTURATI e POSSIBILI TELECAMERE."
        )

    def _set_export_button_enabled(self, which, enabled):
        """
        Abilita/disabilita i pulsanti di esportazione.
        Durante una sessione attiva restano grigi/non cliccabili.
        """
        # ESPORTA HANDSHAKE non deve mai essere attivato genericamente:
        # passa sempre dalla verifica reale del 4-way handshake.
        if which == "handshake":
            self._set_handshake_copy_enabled(bool(enabled))
            return

        attr = "export_capture_button"

        def apply():
            btn = getattr(self, attr, None)
            if btn is None:
                return
            try:
                btn.configure(state=("normal" if enabled else "disabled"))
            except Exception:
                pass

        self.root.after(0, apply)

    def start_diegi_external(self):
        """
        Esegue realmente il programma esterno:
            aireplay-ng -0 0 -a <BSSID> -c <CLIENT> <INTERFACCIA_MONITOR>

        Usa BSSID, client, durata, ripetizioni e attesa gia presenti nella GUI.
        In parallelo mantiene la cattura passiva del programma.
        """
        self.open_diegi_debug()
        self.diegi_debug_write(f"\n[{datetime.now().strftime('%H:%M:%S')}] Pulsante aireplay-ng premuto\n")
        iface=self.validate_monitor_iface()
        if not iface:
            self.diegi_debug_write("[ERRORE] Interfaccia monitor non valida o non disponibile.\n")
            return

        bssid=self.bssid.get().strip().lower()
        ch=self.channel.get().strip()
        client=self.client.get().strip().lower()

        self._dual_band_last_target = (bssid, ch)
        self._dual_band_watch_capture_running = True
        try:
            self.command_debug_write(
                f"[DUAL-BAND] Target CATTURA memorizzato: {bssid} canale {ch}"
            )
        except Exception:
            pass

        if not MAC_FULL.match(bssid):
            messagebox.showwarning("aireplay-ng","Seleziona prima un BSSID/router valido.")
            return
        if not ch.isdigit():
            messagebox.showwarning("aireplay-ng","Il canale selezionato non e valido.")
            return
        if not MAC_FULL.match(client):
            messagebox.showwarning("aireplay-ng","Seleziona prima un MAC client valido.")
            self.diegi_debug_write("[ERRORE] Nessun CLIENT valido selezionato.\n")
            return

        try:
            duration=max(1,int(self.disturb_duration.get()))
            repetitions=max(1,int(self.repetitions.get()))
            pause_seconds=max(0,int(self.pause_seconds.get()))
        except Exception:
            messagebox.showwarning(
                "aireplay-ng",
                "Durata, ripetizioni e attesa devono essere numeri interi."
            )
            return

        # Verifica disponibilita comando.
        if shutil.which("aireplay-ng") is None:
            self.diegi_debug_write("[ERRORE] Comando aireplay-ng non trovato nel PATH.\n")
            messagebox.showerror(
                "aireplay-ng",
                "Il comando aireplay-ng non e stato trovato nel PATH."
            )
            return

        # Tutte le validazioni sono superate: entra in MODALITA' ATTIVA.
        # Il lock resta attivo fino a DUE condizioni contemporanee:
        # 1) aireplay-ng ha completato tutte le ripetizioni previste;
        # 2) la barra della cattura parallela ha realmente raggiunto il 100%.
        self._disturb_active_ui_lock = True
        self._disturb_worker_done = False
        self._set_operation_mode_banner("active")
        self._acquire_suspend_inhibitor("disturb")

        # Pulizia una sola volta all'avvio effettivo di AVVIA DISTURBO.
        self._clear_capture_results_on_start()

        # DISTURBO: barra di lavoro ROSSA e AVVIA lampeggia ROSSO.
        self._set_work_progress_color("red")

        # Finché il DISTURBO è attivo, ESPORTA HANDSHAKE resta grigio.
        self._set_export_button_enabled("handshake", False)
        self._start_button_blink("start_disturb_button")

        self.diegi_stop.clear()
        self.diegi_running = True

        self.logmsg(
            f"aireplay-ng: BSSID={bssid}, client={client}, interfaccia={iface}, "
            f"durata={duration}s, ripetizioni={repetitions}, attesa={pause_seconds}s"
        )

        threading.Thread(
            target=self._diegi_external_worker,
            args=(iface,bssid,client,duration,repetitions,pause_seconds),
            daemon=True
        ).start()

        # Avvia in parallelo la cattura passiva esistente.
        self.handshake_pairs.clear()
        self.handshake_found_async=False
        self.handshake_latched=False
        self.handshake_latched_text=""
        self.handshake_latched_msgs=set()
        self.capture_stop.clear()
        self._restore_handshake_panel_layout()
        self.root.after(0,self.handshake_state.set,self._handshake_word(False))
        self._set_handshake_parts(set())
        self._set_handshake_copy_enabled(False)
        self.root.after(0,self.handshake_string.set,"")
        self.root.after(0, self.pmkid_state.set, "PMKID: non osservato")

        try:
            self.capture_run_id = int(getattr(self, "capture_run_id", 0)) + 1
        except Exception:
            self.capture_run_id = 1
        handshake_run_id = self.capture_run_id

        threading.Thread(
            target=self._capture_worker,
            args=(iface,bssid,ch,client,duration,repetitions,pause_seconds,"handshake",handshake_run_id),
            daemon=True
        ).start()

    def _sync_stop_on_handshake_flag(self):
        """Sincronizza la spunta GUI con un Event thread-safe usato dai worker."""
        if self.stop_on_handshake.get():
            self.stop_on_handshake_event.set()
        else:
            self.stop_on_handshake_event.clear()

    def _finish_disturb_ui_when_complete(self):
        """Chiude la modalità ATTIVA solo dopo cicli aireplay-ng + barra al 100%."""
        try:
            if not bool(getattr(self, "_disturb_active_ui_lock", False)):
                return

            # Se è stato richiesto uno STOP esplicito, la routine di STOP gestisce
            # direttamente lo spegnimento dell'interfaccia.
            if self.diegi_stop.is_set():
                return

            worker_done = bool(getattr(self, "_disturb_worker_done", False))
            try:
                progress = float(self.progress_value.get())
            except Exception:
                progress = 0.0

            # Entrambe le condizioni devono essere vere.
            if worker_done and progress >= 99.95:
                self._disturb_active_ui_lock = False
                self._stop_button_blink("start_disturb_button")
                self._set_operation_mode_banner("idle")
                self._set_handshake_copy_enabled(bool(self.handshake_latched))
                self._release_suspend_inhibitor_later("disturb")
                return

            # Continua a controllare senza interrompere il lampeggio o il banner.
            self.root.after(150, self._finish_disturb_ui_when_complete)
        except Exception as e:
            try:
                self.logmsg(f"Coordinamento fine aireplay-ng: {e}")
            except Exception:
                pass

    def stop_diegi_external(self):
        """Richiede l'arresto immediato del comando DIEGO/aireplay-ng."""
        self.diegi_stop.set()
        proc=self.diegi_process
        if proc is not None and proc.poll() is None:
            try:
                # Il processo viene avviato in una sessione separata: termina tutto il gruppo.
                os.killpg(proc.pid, 15)
            except Exception:
                try:
                    proc.terminate()
                except Exception:
                    pass
        # DISTURBA avvia anche una cattura passiva in parallelo:
        # quando si ferma il disturbo fermiamo anche quella cattura.
        self._stop_capture_process()
        self.set_progress(0, "0%", "PRONTO", "Disturbo e cattura parallela arrestati")
        self.logmsg("Arresto DISTURBO richiesto; cattura parallela fermata e avanzamento azzerato.")
        self.diegi_debug_write("[STOP] Arresto DISTURBO richiesto.\n")
        self.root.after(0, self.set_status, "Disturbo arrestato.")
        # Il comando associato è stato fermato: ora l'esportazione è consentita.
        self._set_handshake_copy_enabled(bool(self.handshake_latched))
        self._disturb_active_ui_lock = False
        self._disturb_worker_done = False
        self._stop_button_blink("start_disturb_button")
        self._set_operation_mode_banner("idle")
        self._release_suspend_inhibitor_later("disturb")

    def stop_capture(self):
        try:
            _dual_bssid = self._dual_band_value(getattr(self,"bssid",""))
            _dual_channel = self._dual_band_value(getattr(self,"channel",""))
        except Exception:
            _dual_bssid, _dual_channel = "", ""
        """Ferma la cattura passiva e azzera immediatamente la barra di avanzamento."""
        self._stop_capture_process()
        self.set_progress(0, "0%", "PRONTO", "Cattura passiva arrestata")
        self.root.after(0, self.set_status, "Cattura passiva arrestata.")
        self.logmsg("Cattura passiva arrestata manualmente; avanzamento azzerato.")
        # Il comando associato è stato fermato: ora l'esportazione è consentita.
        self._set_export_button_enabled("capture", True)
        self._stop_button_blink("start_capture_button")
        self._stop_passive_mode_banner_blink()
        self._manual_capture_banner_active = False
        self._set_operation_mode_banner("idle")
        self._release_suspend_inhibitor_later("capture")
        # STOP manuale: il controllo dual-band deve avvenire comunque.
        # Usiamo after_idle + due retry brevi per lasciare terminare gli ultimi
        # aggiornamenti della GUI/tabella router senza dipendere dal worker.
        try:
            self._dual_band_watch_capture_running = False
            self.root.after_idle(
                lambda _b=_dual_bssid,_c=_dual_channel:
                    self._dual_band_check_after_manual_stop(_b,_c)
            )
            self.root.after(
                700,
                lambda _b=_dual_bssid,_c=_dual_channel:
                    self._dual_band_check_after_manual_stop(_b,_c)
            )
            self.root.after(
                1800,
                lambda _b=_dual_bssid,_c=_dual_channel:
                    self._dual_band_check_after_manual_stop(_b,_c)
            )
        except Exception as e:
            try:
                self.command_debug_write(
                    f"[DUAL-BAND] STOP manuale: impossibile pianificare controllo: {e}"
                )
            except Exception:
                pass


    def _stop_capture_process(self):
        """Ferma airodump-ng e invalida immediatamente la sessione di cattura corrente."""
        self.capture_stop.set()

        # Invalida il worker corrente: anche se sta terminando analisi/snapshot
        # in background non potrà più modificare barra/stato della cattura successiva.
        try:
            self.capture_run_id = int(getattr(self, "capture_run_id", 0)) + 1
        except Exception:
            self.capture_run_id = 1

        proc=self.capture_process
        if proc is not None and proc.poll() is None:
            try:
                proc.terminate()
                proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                try:
                    proc.kill()
                    proc.wait(timeout=1)
                except Exception:
                    pass
            except Exception as e:
                self.logmsg(f"Arresto cattura PCAP: {e}")

    def _stop_all_on_handshake(self):
        """Arresto coordinato richiesto dalla spunta: DIEGO + cattura PCAP."""
        self.diegi_stop.set()
        self.capture_stop.set()
        self.stop_diegi_external()
        self._stop_capture_process()
        self._set_operation_mode_banner("idle")
        self.root.after(0, self.set_status, "Handshake trovato: DIEGO e cattura arrestati.")

    def _diegi_external_worker(self, iface, bssid, client, duration, repetitions, pause_seconds):
        """
        Ogni ripetizione rappresenta una finestra temporale reale di `duration`
        secondi. Se aireplay-ng termina autonomamente prima della scadenza, viene
        rilanciato nella stessa finestra così il monitoraggio copre tutto il
        periodo richiesto.
        """
        cmd=["aireplay-ng","-0","0","-a",bssid,"-c",client,iface]
        self.diegi_debug_write(f"$ {' '.join(cmd)}\n")

        duration=max(1,int(duration))
        repetitions=max(1,int(repetitions))
        pause_seconds=max(0,int(pause_seconds))

        for cycle in range(1,repetitions+1):
            if self.diegi_stop.is_set():
                break
            window_start=time.monotonic()
            window_end=window_start+duration
            launches=0

            self.logmsg(
                f"aireplay-ng {cycle}/{repetitions}: finestra={duration}s, "
                f"comando=$ {' '.join(cmd)}"
            )

            while time.monotonic() < window_end:
                if self.diegi_stop.is_set():
                    break
                launches += 1
                remaining_before=max(0.0,window_end-time.monotonic())

                self.logmsg(
                    f"aireplay-ng {cycle}/{repetitions}: avvio #{launches}, "
                    f"tempo finestra residuo={remaining_before:.1f}s"
                )

                try:
                    proc=popen_logged(
                        cmd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                        text=True,
                        bufsize=1,
                        start_new_session=True
                    )
                    self.diegi_process = proc
                except Exception as e:
                    self.logmsg(f"Errore avvio aireplay-ng: {e}")
                    self.diegi_debug_write(f"[ERRORE AVVIO] {e}\n")
                    self.root.after(
                        0,
                        self.set_status,
                        "Errore avvio programma aireplay-ng"
                    )
                    return

                def reader(p, cyc, launch_no):
                    try:
                        if p.stdout:
                            for line in iter(p.stdout.readline, ""):
                                if not line:
                                    break
                                clean=line.rstrip("\n")
                                self.logmsg(
                                    f"aireplay-ng[{cyc}#{launch_no}]: {clean}"
                                )
                                self.diegi_debug_write(clean+"\n")
                    except Exception as e:
                        self.logmsg(f"aireplay-ng output: {e}")
                        self.diegi_debug_write(f"[ERRORE OUTPUT] {e}\n")

                threading.Thread(
                    target=reader,
                    args=(proc,cycle,launches),
                    daemon=True
                ).start()

                process_start=time.monotonic()

                while True:
                    now=time.monotonic()
                    remaining=max(0.0,window_end-now)

                    self.root.after(
                        0,
                        self.set_status,
                        f"aireplay-ng {cycle}/{repetitions} - "
                        f"{int(round(remaining))}s rimanenti"
                    )

                    if self.diegi_stop.is_set():
                        break

                    if self.handshake_found_async and self.stop_on_handshake_event.is_set():
                        self.diegi_stop.set()
                        self.logmsg("Handshake completo: arresto automatico DIEGO richiesto.")
                        break

                    if remaining <= 0:
                        break

                    rc=proc.poll()
                    if rc is not None:
                        self.logmsg(
                            f"aireplay-ng {cycle}/{repetitions} avvio #{launches} "
                            f"terminato dopo {time.monotonic()-process_start:.1f}s "
                            f"(exit={rc})."
                        )
                        break

                    time.sleep(0.20)

                # Al termine della finestra o su STOP/handshake, termina l'istanza attiva.
                if (time.monotonic() >= window_end or self.diegi_stop.is_set()) and proc.poll() is None:
                    try:
                        proc.terminate()
                        proc.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        try:
                            proc.kill()
                            proc.wait(timeout=2)
                        except Exception:
                            pass
                    except Exception as e:
                        self.logmsg(f"Terminazione aireplay-ng: {e}")

                # Se la finestra non è ancora finita e DIEGO è uscito,
                # rilancialo. Una piccola attesa evita loop rapidissimi in
                # caso di errore immediato del programma.
                if time.monotonic() < window_end and not self.diegi_stop.is_set():
                    time.sleep(0.25)

            effective=time.monotonic()-window_start
            self.logmsg(
                f"aireplay-ng {cycle}/{repetitions}: finestra completata, "
                f"durata effettiva={effective:.1f}s, avvii={launches}."
            )

            if self.diegi_stop.is_set():
                break

            # Pausa reale tra le ripetizioni.
            if cycle < repetitions and pause_seconds > 0:
                pause_start=time.monotonic()
                while True:
                    if self.diegi_stop.is_set():
                        break
                    elapsed=time.monotonic()-pause_start
                    if elapsed >= pause_seconds:
                        break
                    left=max(0,int(round(pause_seconds-elapsed)))
                    self.root.after(
                        0,
                        self.set_status,
                        f"aireplay-ng - pausa {left}s prima della ripetizione "
                        f"{cycle+1}/{repetitions}"
                    )
                    time.sleep(0.20)

        self.diegi_process = None
        self.diegi_running = False
        if self.diegi_stop.is_set():
            self.root.after(0, self.set_status, "DIEGO terminato.")
            self.diegi_debug_write("[STOP] DIEGO terminato.\n")
        else:
            self.root.after(
                0,
                self.set_status,
                f"aireplay-ng completato: {repetitions} ripetizioni."
            )

        # aireplay-ng ha concluso il proprio worker. In caso di fine naturale NON
        # spegniamo qui AVVIA e MODALITA' ATTIVA: devono restare attivi finché
        # anche la cattura parallela non ha raggiunto realmente il 100%.
        if self.diegi_stop.is_set():
            # Lo STOP esplicito viene già gestito dalla routine dedicata.
            pass
        else:
            self._disturb_worker_done = True
            self.root.after(0, self._finish_disturb_ui_when_complete)


    def start_capture(self):
        iface=self.validate_monitor_iface()
        if not iface:
            return
        bssid=self.bssid.get().strip().lower()
        ch=self.channel.get().strip()
        client=self.client.get().strip().lower()

        if not MAC_FULL.match(bssid):
            messagebox.showwarning("BSSID","Seleziona un router dall'elenco.")
            return
        if not ch.isdigit():
            messagebox.showwarning("Canale","Canale non valido.")
            return
        if client and not MAC_FULL.match(client):
            messagebox.showwarning("Client","MAC client non valido.")
            return

        # Nuovo AVVIA oppure continuazione di una seconda scansione proposta dal sistema.
        # La decisione viene presa PRIMA di creare il nuovo segmento PCAP.
        try:
            self._capture_chain_prepare_start(bssid)
        except Exception as e:
            try:
                self.logmsg(f"Preparazione PCAP multi-scansione: {e}")
            except Exception:
                pass

        # Identifica il segmento PASSIVO corrente. Se è una continuazione
        # correlata, il reason distingue DUAL-BAND da ROUTER IN CASCATA.
        try:
            _passive_relation = (
                str(getattr(self, "_capture_chain_current_reason", "") or "")
                if getattr(self, "_capture_chain_current_continuation", False)
                else ""
            )
            self._passive_current_source_bssid = bssid
            self._passive_current_source_label = self._scan_source_label(
                "passive", bssid, ch, _passive_relation
            )

            # Una cattura manuale NON correlata apre un nuovo insieme visivo.
            if not getattr(self, "_capture_chain_current_continuation", False):
                self._camera_capture_sources = {}
                self._camera_capture_bssids = {}
                self._lan_display_sources = {}
        except Exception:
            pass

        try:
            _chain_reason = str(
                getattr(self, "_capture_chain_current_reason", "") or ""
            ).strip().lower()
            _is_cont = bool(
                getattr(self, "_capture_chain_current_continuation", False)
            )
            if (not _is_cont) or ("cascade" in _chain_reason):
                self._passive_router_stage_reset(bssid)
        except Exception:
            pass

        try:
            duration=max(10,int(self.capture_duration.get()))
        except:
            duration=120
        repetitions=1
        pause_seconds=0

        # Nuovo AVVIA = nuova sessione completa.
        # Invalida qualunque worker precedente e riparte sempre da 0%.
        try:
            self.capture_run_id = int(getattr(self, "capture_run_id", 0)) + 1
        except Exception:
            self.capture_run_id = 1
        run_id = self.capture_run_id
        self.capture_stop.clear()
        self.capture_process = None
        self.set_progress(
            0, "0%",
            "PREPARATION" if getattr(self,"language","it")=="en" else "PREPARAZIONE",
            "New capture session" if getattr(self,"language","it")=="en"
            else "Nuova sessione di cattura"
        )

        # MODALITA' PASSIVA / PASSIVE MODE resta visibile in blu
        # per TUTTA la cattura, ma NON lampeggia. Il lock impedisce ad altre
        # callback di riportare il banner su IDLE/ATTIVA mentre il PCAP è in corso.
        self._manual_capture_banner_active = True
        self._stop_passive_mode_banner_blink()
        self._set_operation_mode_banner("passive")

        self._acquire_suspend_inhibitor("capture")

        # Pulizia una sola volta all'avvio effettivo di AVVIA CATTURA.
        self._clear_capture_results_on_start()

        # LAN PASSIVA STRICT:
        # nessuna discovery ARP/ping/nmap viene avviata automaticamente.
        # La classificazione LAN usa esclusivamente gli header 802.11 presenti
        # nel PCAP della cattura e la prova radio osservata nello stesso PCAP.

        # CATTURA PASSIVA: barra di lavoro BLU e AVVIA lampeggia BLU.
        self._set_work_progress_color("blue")

        # Finché la CATTURA PASSIVA è attiva, ESPORTA CATTURA resta grigio.
        self._set_export_button_enabled("capture", False)

        # ESPORTA HANDSHAKE resta grigio finché non viene realmente ricostruito
        # un 4-way completo, anche durante la cattura passiva.
        self._set_handshake_copy_enabled(False)

        self._start_button_blink("start_capture_button")

        self.handshake_pairs.clear()
        self.handshake_found_async=False
        self.handshake_latched=False
        self.handshake_latched_text=""
        self.handshake_latched_msgs=set()
        self._restore_handshake_panel_layout()
        self.root.after(0, self.handshake_state.set, self._handshake_word(False))
        self._set_handshake_parts(set())
        self._set_handshake_copy_enabled(False)
        self.root.after(0, self.handshake_string.set, "")
        self.root.after(0, self.pmkid_state.set, "PMKID: non osservato")
        self.set_progress(0, "0%", "PREPARAZIONE", "Impostazione canale e parametri di cattura")
        threading.Thread(
            target=self._capture_worker,
            args=(iface,bssid,ch,client,duration,repetitions,pause_seconds,"manual",run_id),
            daemon=True
        ).start()

    def _start_async_handshake_check(self, cap, bssid, stop_on_found=False):
        """Avvia il controllo EAPOL senza bloccare timer e percentuale della cattura."""
        if self.handshake_check_running:
            return
        if not cap or not Path(cap).exists():
            return

        self.handshake_check_running = True

        def worker():
            snapshot=None
            try:
                # Durante la cattura airodump-ng sta ancora scrivendo il PCAP.
                # TShark può quindi trovare un ultimo pacchetto incompleto e
                # restituire un codice != 0 pur avendo già estratto EAPOL validi.
                # Analizziamo una copia congelata del file per evitare letture
                # concorrenti e falsi "ERRORE LETTURA EAPOL".
                src=Path(cap)
                snapshot=src.with_name(src.stem + ".eapol_snapshot" + src.suffix)
                try:
                    shutil.copyfile(src, snapshot)
                    target=snapshot
                except Exception as copy_err:
                    self.logmsg(f"Snapshot EAPOL non disponibile, uso file live: {copy_err}")
                    target=src

                if self.check_handshake(target, bssid, stop_on_found=stop_on_found):
                    self.handshake_found_async = True
            except Exception as e:
                self.logmsg(f"Controllo handshake non bloccante: {e}")
            finally:
                if snapshot is not None:
                    try:
                        snapshot.unlink(missing_ok=True)
                    except Exception:
                        pass
                self.handshake_check_running = False

        threading.Thread(target=worker, daemon=True).start()

    def _merge_live_mac_rows(self, rows, replace=False):
        """Aggiorna MAC/LAN; il risultato finale puo' sostituire gli snapshot live.

        Durante la cattura gli aggiornamenti live restano incrementali per evitare
        flicker. Alla fine, invece, ``replace=True`` rende il PCAP definitivo la
        fonte autorevole: righe comparse solo in snapshot parziali vengono rimosse.
        """
        incoming = {}
        for row in rows or []:
            if len(row) < 5:
                continue
            mac, vendor, cls, evidence, notes = row[:5]
            mac = str(mac).lower()
            if not MAC_FULL.match(mac):
                continue
            incoming[mac] = (mac, vendor, cls, evidence, notes)

        changed = False
        if replace:
            # Il PCAP finale prevale sugli snapshot live. Questo evita candidati
            # LAN/MAC "fantasma" rimasti visibili dopo analisi parziali.
            old_map = dict(getattr(self, "live_mac_rows", {}) or {})
            self.live_mac_rows = dict(incoming)
            changed = old_map != self.live_mac_rows

            # Anche le cache LAN sticky devono essere ricostruite dal risultato
            # finale; la seconda scansione cascata reintegrera' poi le righe della
            # prima tramite _cascade_first_lan_* come gia' previsto.
            self.lan_seen_rows = {}
            self.lan_candidate_details = {}
            self.lan_persistent_rows = {}
            self.lan_persistent_details = {}
            self.lan_candidate_confirmations = {}
            self.lan_low_traffic_history = {}
            self.lan_confirmed_visible = set()
        else:
            if not isinstance(getattr(self, "live_mac_rows", None), dict):
                self.live_mac_rows = {}
            for mac, current in incoming.items():
                old = self.live_mac_rows.get(mac)
                if old != current:
                    self.live_mac_rows[mac] = current
                    changed = True

        # Indicizza per (MAC, PROVENIENZA): lo stesso MAC può comparire in
        # due segmenti correlati senza cancellare la cattura precedente.
        current_source = str(
            getattr(self, "_passive_current_source_label", "") or ""
        ).strip()

        visible = {}
        for item in self.res_tree.get_children():
            vals = tuple(self.res_tree.item(item, "values") or ())
            if vals:
                mac0 = str(vals[0]).lower()
                src0 = str(vals[5] if len(vals) > 5 else "")
                visible[(mac0, src0)] = item

        if replace:
            # Rimuove soltanto le righe obsolete DEL SEGMENTO CORRENTE.
            # Le righe con un'altra provenienza appartengono alle catture precedenti.
            for (mac0, src0), item in list(visible.items()):
                if src0 == current_source and mac0 not in self.live_mac_rows:
                    try:
                        self.res_tree.delete(item)
                    except Exception:
                        pass
                    visible.pop((mac0, src0), None)
                    changed = True

        for mac in sorted(self.live_mac_rows):
            row = self.live_mac_rows[mac]
            translated = tuple(self._mac_row_for_language(row))
            display = translated + (current_source,)
            key = (mac, current_source)
            item = visible.get(key)
            if item:
                current_vals = tuple(self.res_tree.item(item, "values")[:6])
                if current_vals != display:
                    self.res_tree.item(item, values=display)
                    changed = True
            else:
                self.res_tree.insert("", "end", values=display)
                changed = True

        # Anche se la mappa non e' cambiata, in replace=True dobbiamo comunque
        # ricostruire la tabella LAN dalle sole righe definitive.
        if not changed and not replace:
            return

        normalized = list(self.live_mac_rows.values())
        wifi_clients = sum(1 for r in normalized if r[2] == "Wi-Fi ASSOCIATO")
        lan_candidates = sum(1 for r in normalized if r[2] == "LAN CANDIDATO")
        other = sum(1 for r in normalized if r[2] == "ALTRO/INCERTO")

        if self.language == "en":
            self.lan_count.set(f"LAN-side candidates (not confirmed): {lan_candidates}")
            self.other_count.set(f"Other / uncertain: {other}")
        else:
            self.lan_count.set(f"LAN candidati (non certi): {lan_candidates}")
            self.other_count.set(f"Altro/incerto: {other}")
        self.update_probable_lan_vendors(normalized)

    def _merge_camera_candidate_rows(self, rows):
        # Integrazione scansione cascata: i risultati precedenti restano visibili.
        try:
            if getattr(self, "_cascade_first_camera_details", None):
                for _m,_d in self._cascade_first_camera_details.items():
                    self.camera_candidate_details.setdefault(_m, _d)
        except Exception:
            pass
        """
        Aggiorna POSSIBILI TELECAMERE RILEVATE senza svuotare la Treeview.

        Le righe gia' visibili vengono aggiornate in-place usando il MAC come iid;
        questo evita il fastidioso lampeggio causato dal precedente delete/insert
        completo ad ogni analisi live. Poiché ogni analisi rilegge l'intero PCAP,
        i candidati che non superano più il filtro vengono rimossi: niente falsi
        positivi persistenti o righe "fantasma".
        """
        if not hasattr(self, "camera_tree"):
            return

        # Memoria usata solo per aggiornare le righe senza flicker; lo snapshot
        # corrente dell'intero PCAP decide quali candidati devono restare visibili.
        if not isinstance(getattr(self, "camera_candidate_rows", None), dict):
            self.camera_candidate_rows = {}

        changed_macs = []

        # analyze_camera_candidates() analizza ogni volta l'intero PCAP corrente.
        # Quindi "rows" è uno snapshot completo, non un delta. La vecchia logica
        # conservava invece per sempre i candidati comparsi in un'analisi iniziale:
        # questo generava falsi positivi "fantasma" anche quando il PCAP completo
        # non conteneva più alcuna evidenza sufficiente.
        current_rows = {}

        # Candidati provenienti dalla sola scansione CLIENT (vendor/OUI fortemente
        # orientato a telecamera) restano come POSSIBILE anche se la cattura
        # passiva non contiene DATA utile.
        try:
            for _m, _r in (getattr(self, "camera_candidate_rows", {}) or {}).items():
                _d = (getattr(self, "camera_candidate_details", {}) or {}).get(_m, {}) or {}
                if _d.get("client_identity_candidate"):
                    current_rows[str(_m).lower()] = tuple(_r)
        except Exception:
            pass

        _camera_blocked_bssids = set(self._known_ap_bssids())
        try:
            _cb = str(self._dual_band_value(getattr(self,"bssid","")) or "").strip().lower()
            if MAC_FULL.match(_cb):
                _camera_blocked_bssids.add(_cb)
        except Exception:
            pass
        for row in rows or []:
            if len(row) < 8:
                continue
            row = tuple(row[:8])
            mac = str(row[0]).replace("(*)","").strip().lower()
            vendor = str(row[1] if len(row) > 1 else "")
            if not MAC_FULL.match(mac):
                continue
            if mac in _camera_blocked_bssids:
                continue
            try:
                if self._is_camera_infrastructure_mac(mac, vendor):
                    continue
            except Exception:
                pass
            current_rows[mac] = row

        # Safety net GUI: un BSSID/AP non puo' restare come telecamera nemmeno
        # se una vecchia cache o un algoritmo secondario lo aveva inserito.
        for _apmac in list(_camera_blocked_bssids):
            self.camera_candidate_rows.pop(_apmac, None)
            self.camera_candidate_details.pop(_apmac, None)
            try:
                if self.camera_tree.exists(_apmac):
                    self.camera_tree.delete(_apmac)
            except Exception:
                pass
        # Elimina anche interfacce LAN/WAN adiacenti dello stesso router
        # (es. BSSID ...:16 e interfaccia ...:17) se erano rimaste in cache.
        for _mac0, _row0 in list(self.camera_candidate_rows.items()):
            try:
                _vend0 = str(_row0[1] if len(_row0) > 1 else "")
                if not self._is_camera_infrastructure_mac(_mac0, _vend0):
                    continue
                self.camera_candidate_rows.pop(_mac0, None)
                self.camera_candidate_details.pop(_mac0, None)
                if self.camera_tree.exists(_mac0):
                    self.camera_tree.delete(_mac0)
            except Exception:
                pass

        # Router-cascata:
        # la sostituzione del placeholder viene fatta SOLO nel merge FINALE
        # della seconda scansione. I merge live non devono consumare il
        # placeholder né scegliere prematuramente un candidato sbagliato.
        if (getattr(self, "_cascade_router_cam_integration_active", False)
                and getattr(self, "_cascade_router_cam_finalize_merge", False)):
            try:
                _ph = set(getattr(self, "_cascade_router_cam_placeholders", set()) or set())
                _real = []
                for _mac, _row0 in list(current_rows.items()):
                    if _mac in _ph:
                        continue
                    _det = (getattr(self, "camera_candidate_details", {}) or {}).get(_mac, {}) or {}
                    if _det.get("nvr_candidate") or _det.get("cascade_camera_candidate"):
                        continue

                    # Nella seconda scansione il dispositivo dietro il router
                    # puo' essere sia cablato sia Wi-Fi. Entrambe le provenienze
                    # sono valide; la colonna PROVENIENZA mantiene la distinzione.
                    try:
                        _prov = str(_row0[5] if len(_row0) > 5 else "").strip().upper()
                    except Exception:
                        _prov = ""
                    _det_prov = str(_det.get("provenance","") or "").strip().upper()
                    _prov_all = {_prov, _det_prov}
                    if not any(p in ("LAN", "WIFI", "WI-FI") for p in _prov_all):
                        continue

                    _real.append(_mac)

                if _real:
                    # Rimuove la riga WAN/router della prima scansione.
                    for _pmac in _ph:
                        self.camera_candidate_rows.pop(_pmac, None)
                        self.camera_candidate_details.pop(_pmac, None)
                        if self.camera_tree.exists(_pmac):
                            self.camera_tree.delete(_pmac)

                    # Marca le camere reali trovate nella seconda scansione.
                    for _mac in _real:
                        _row = list(current_rows[_mac])
                        # tuple: MAC,VENDOR,SCORE,PROBABILITA,TXRX,PROVENIENZA,DURATA,NOTE
                        if len(_row) >= 6:
                            # Mantieni SEMPRE la scala di probabilita' originale
                            # (MOLTO PROBABILE / PROBABILE / POSSIBILE / DA OSSERVARE).
                            # ROUTER-CAM descrive la relazione/topologia e va quindi
                            # nella PROVENIENZA, non al posto della probabilita'.
                            _orig_prov = str(_row[5] or "").strip().upper()
                            if _orig_prov in ("WIFI", "WI-FI"):
                                _row[5] = "WIFI ROUTER-CAM"
                            else:
                                _row[5] = "LAN ROUTER-CAM"
                        current_rows[_mac] = tuple(_row)

                        _det = self.camera_candidate_details.setdefault(_mac, {})
                        _orig_det_prov = str(_det.get("provenance", "") or "").strip().upper()
                        if _orig_det_prov in ("WIFI", "WI-FI"):
                            _det["provenance"] = "WIFI"
                            _det["source_display"] = "WIFI ROUTER-CAM"
                        else:
                            _det["provenance"] = "LAN"
                            _det["source_display"] = "LAN ROUTER-CAM"
                        # NON sovrascrivere level/probability: la scala resta intatta.
                        _det["router_cam_confirmed"] = True
                        _det["cascade_parent_bssid"] = getattr(
                            self, "_cascade_second_scan_target_bssid", ""
                        )

                        # Dettagli espliciti della correlazione router/BSSID
                        # che ha portato alla seconda scansione.
                        _match = getattr(self, "_cascade_pending_match", {}) or {}
                        _router_mac = str(_match.get("wan_mac","") or "")
                        _corr_bssid = str(_match.get("bssid","") or getattr(
                            self, "_cascade_second_scan_target_bssid", ""
                        ) or "")
                        _corr_channel = str(_match.get("channel","") or getattr(
                            self, "_cascade_second_scan_target_channel", ""
                        ) or "")
                        _corr_score = str(_match.get("score","") or "")
                        _corr_ssid = str(_match.get("ssid","") or "")
                        _corr_reasons = _match.get("reasons", []) or []

                        _is_en = getattr(self, "language", "it") == "en"
                        if _is_en:
                            _corr_lines = [
                                "=== ROUTER-CAM DETECTION PATH ===",
                                "Detected during the SECOND passive scan on the correlated BSSID.",
                                f"Router WAN/LAN MAC from first scan: {_router_mac or '-'}",
                                f"Correlated Wi-Fi BSSID: {_corr_bssid or '-'}",
                                f"SSID: {_corr_ssid or '-'}",
                                f"Channel: {_corr_channel or '-'}",
                                f"Router/BSSID correlation score: {_corr_score + '/100' if _corr_score else '-'}",
                            ]
                            if _corr_reasons:
                                _corr_lines.append("Correlation evidence: " + ", ".join(map(str, _corr_reasons)))
                            _corr_lines += [
                                "",
                                "This device was not confirmed from the first router-side capture alone.",
                                "It was identified after switching to the correlated second BSSID and running the dedicated second passive scan.",
                            ]
                        else:
                            _corr_lines = [
                                "=== PERCORSO DI RILEVAMENTO ROUTER-CAM ===",
                                "Rilevata durante la SECONDA scansione passiva sul BSSID correlato.",
                                f"MAC WAN/LAN router rilevato nella prima scansione: {_router_mac or '-'}",
                                f"BSSID Wi-Fi correlato: {_corr_bssid or '-'}",
                                f"SSID: {_corr_ssid or '-'}",
                                f"Canale: {_corr_channel or '-'}",
                                f"Score correlazione router/BSSID: {_corr_score + '/100' if _corr_score else '-'}",
                            ]
                            if _corr_reasons:
                                _corr_lines.append("Evidenze correlazione: " + ", ".join(map(str, _corr_reasons)))
                            _corr_lines += [
                                "",
                                "Il dispositivo non e' stato confermato dalla sola prima cattura lato router.",
                                "E' stato individuato dopo il passaggio al secondo BSSID correlato e la successiva scansione passiva dedicata.",
                            ]

                        _existing_extra = str(_det.get("details_extra","") or "").strip()
                        _corr_text = "\n".join(_corr_lines)
                        _det["details_extra"] = (
                            (_existing_extra + "\n\n" + _corr_text)
                            if _existing_extra else _corr_text
                        )

                    self._cascade_router_cam_placeholders = set()
                    self._cascade_router_cam_integration_active = False
            except Exception as _e:
                self.logmsg(f"Router-CAM merge: {_e}")

        # Stabilizzazione live: una telecamera già confermata e visualizzata
        # resta visibile per tutta la cattura corrente. Le analisi successive possono
        # aggiornare i suoi valori, ma non la eliminano per un singolo snapshot
        # temporaneamente sotto soglia o per callback che arrivano fuori ordine.
        # La normale inizializzazione di una NUOVA cattura azzera camera_candidate_rows,
        # quindi la stabilizzazione non trascina risultati nella cattura successiva.
        stale_macs = set(self.camera_candidate_rows) - set(current_rows)
        for mac in stale_macs:
            try:
                if self.camera_tree.exists(mac):
                    # Mantiene la riga esistente senza delete/insert: niente
                    # comparsa/scomparsa durante la cattura passiva.
                    pass
            except Exception:
                pass

        for mac, row in current_rows.items():
            old = self.camera_candidate_rows.get(mac)
            self.camera_candidate_rows[mac] = row

            # Se il MAC era gia' presente nella prima scansione, il nuovo
            # risultato della seconda cattura ha priorita' per valori/dettagli.
            try:
                _new_det = getattr(self, "camera_candidate_details", {}).get(mac)
                if _new_det is not None:
                    self.camera_candidate_details[mac] = _new_det
            except Exception:
                pass

            # MAC usato come identificatore stabile della riga. In questo modo
            # item() modifica soltanto i valori senza far scomparire la tabella.
            display_row = self._camera_display_row_with_scan_source(mac, row)
            if self.camera_tree.exists(mac):
                if old != row or tuple(self.camera_tree.item(mac, "values") or ()) != display_row:
                    self.camera_tree.item(mac, values=display_row)
                    changed_macs.append(mac)
            else:
                self.camera_tree.insert("", "end", iid=mac, values=display_row)
                changed_macs.append(mac)

        # Riordina gli elementi esistenti SENZA cancellarli/reinserirli. move()
        # conserva i widget e quindi non produce il flash bianco della Treeview.
        def score_of(row):
            try:
                return int(str(row[2]).split('/')[0] or 0)
            except Exception:
                return 0

        ordered = sorted(
            self.camera_candidate_rows.items(),
            key=lambda kv: (-score_of(kv[1]), str(kv[0]))
        )
        for pos, (mac, _row) in enumerate(ordered):
            if self.camera_tree.exists(mac):
                try:
                    self.camera_tree.move(mac, "", pos)
                except Exception:
                    pass
        # Aggiorna subito il contatore mentre vengono rilevati nuovi candidati.
        try:
            self._refresh_result_counters()
        except Exception:
            pass
        self._refresh_camera_block_action()
        try:
            self._network_graph_snapshot_current(None, "camera analysis")
        except Exception:
            pass


    def _cascade_realtime_camera_association(self, rows):
        """Associazione GUI in TEMPO REALE durante la seconda scansione.

        E' un livello separato: non modifica gli algoritmi camera/LAN/NVR/cascade.
        Appena il normale algoritmo camera produce una camera LAN o WIFI:
        - elimina subito CAM DIETRO ROUTER;
        - mostra la camera reale;
        - aggiunge (*) alla PROVENIENZA della camera;
        - aggiunge (*) al MAC del router nella tabella LAN;
        - aggiorna i dettagli di entrambi.
        """
        if not getattr(self, "_cascade_second_scan_running", False):
            return

        match = getattr(self, "_cascade_pending_match", {}) or {}
        parent_mac = str(match.get("wan_mac","") or "").strip().lower()
        parent_bssid = str(match.get("bssid","") or getattr(
            self, "_cascade_second_scan_target_bssid", ""
        ) or "").strip().lower()
        placeholders = set(getattr(self, "_cascade_router_cam_placeholders", set()) or set())

        found = {}
        for row in rows or []:
            if not row:
                continue
            mac = str(row[0] if len(row)>0 else "").replace("(*)","").strip().lower()
            if not MAC_FULL.match(mac) or mac in placeholders:
                continue
            det = (getattr(self,"camera_candidate_details",{}) or {}).get(mac,{}) or {}
            if det.get("nvr_candidate") or det.get("cascade_camera_candidate"):
                continue

            prov = str(det.get("provenance","") or "").strip().upper()
            if prov not in ("LAN","WIFI","WI-FI"):
                try:
                    prov = str(row[5] if len(row)>5 else "").strip().upper()
                except Exception:
                    prov = ""
            if prov in ("WIFI","WI-FI"):
                prov = "WIFI"
            elif prov == "LAN":
                prov = "LAN"
            else:
                continue
            found[mac] = (tuple(row), prov)

        if not found:
            return

        # Persistenza della relazione per tutta la seconda scansione.
        if not isinstance(getattr(self,"_cascade_second_scan_cameras",None),dict):
            self._cascade_second_scan_cameras={}
        for mac,(row,prov) in found.items():
            self._cascade_second_scan_cameras[mac] = {
                "provenance":prov, "parent_mac":parent_mac,
                "parent_bssid":parent_bssid, "row":row
            }

        # 1. CAM DIETRO ROUTER sparisce IMMEDIATAMENTE.
        for pmac in placeholders:
            self.camera_candidate_rows.pop(pmac,None)
            self.camera_candidate_details.pop(pmac,None)
            try:
                if self.camera_tree.exists(pmac):
                    self.camera_tree.delete(pmac)
            except Exception:
                pass
            try:
                for iid in list(self.camera_tree.get_children("")):
                    vals=self.camera_tree.item(iid,"values") or ()
                    if vals and str(vals[0]).replace("(*)","").strip().lower()==pmac:
                        self.camera_tree.delete(iid)
            except Exception:
                pass

        # Impedisce ai successivi refresh della seconda scansione di ripristinare
        # il placeholder dalla memoria della prima scansione.
        try:
            for pmac in placeholders:
                getattr(self,"_cascade_first_camera_rows",{}).pop(pmac,None)
                getattr(self,"_cascade_first_camera_details",{}).pop(pmac,None)
        except Exception:
            pass

        # 2. Merge normale delle camere reali, poi sola annotazione visuale.
        clean_rows=[]
        for row in rows or []:
            mac=str(row[0] if row else "").replace("(*)","").strip().lower()
            if mac not in placeholders:
                clean_rows.append(row)
        self._merge_camera_candidate_rows(clean_rows)

        allcams=dict(getattr(self,"_cascade_second_scan_cameras",{}) or {})
        is_en=getattr(self,"language","it")=="en"
        corr_score=match.get("score","")
        corr_ssid=str(match.get("ssid","") or "")
        corr_ch=str(match.get("channel","") or "")

        for mac,info in allcams.items():
            prov=info.get("provenance","")
            # Camera table: MAC e vendor REALI; asterisco SOLO in PROVENIENZA.
            try:
                for iid in self.camera_tree.get_children(""):
                    vals=list(self.camera_tree.item(iid,"values") or ())
                    if not vals: continue
                    raw=str(vals[0]).replace("(*)","").strip().lower()
                    if raw!=mac: continue
                    vals[0]=mac.upper()
                    if len(vals)>5:
                        vals[5]=prov+" (*)"
                    try:
                        vendor=str(self.resolve_mac_with_manuf(mac) or "").strip()
                    except Exception:
                        vendor=""
                    if vendor and len(vals)>1:
                        vals[1]=vendor
                    self.camera_tree.item(iid,values=tuple(vals))
            except Exception:
                pass

            det=self.camera_candidate_details.setdefault(mac,{})
            det["provenance"]=prov
            det["source_display"]=prov+" (*)"
            det["second_scan_camera"]=True
            det["router_cam_parent_mac"]=parent_mac
            det["router_cam_parent_bssid"]=parent_bssid
            marker="=== SECOND-SCAN ROUTER ASSOCIATION ===" if is_en else "=== ASSOCIAZIONE ROUTER - SECONDA SCANSIONE ==="
            extra=str(det.get("details_extra","") or "")
            if marker not in extra:
                lines=[
                    marker,
                    ("Camera detected in REAL TIME during the SECOND passive scan."
                     if is_en else
                     "Telecamera rilevata IN TEMPO REALE durante la SECONDA scansione passiva."),
                    (f"Associated router MAC: {parent_mac or '-'}"
                     if is_en else f"MAC router associato: {parent_mac or '-'}"),
                    f"BSSID: {parent_bssid or '-'}",
                    f"SSID: {corr_ssid or '-'}",
                    ("Channel: " if is_en else "Canale: ")+(corr_ch or "-"),
                    ("Source: " if is_en else "Provenienza: ")+prov+" (*)",
                    ("Router/BSSID correlation: " if is_en else "Correlazione router/BSSID: ")
                    +((str(corr_score)+"/100") if corr_score!="" else "-"),
                    ("The (*) links this camera to the router marked (*) in the LAN table."
                     if is_en else
                     "L'asterisco (*) collega questa telecamera al router marcato (*) nella tabella LAN.")
                ]
                det["details_extra"]=extra+("\n\n" if extra else "")+"\n".join(lines)

        # 3. LAN: asterisco nella colonna RUOLO/ROLE del router associato,
        # in tempo reale. La tabella reale e' lan_vendor_tree:
        # VENDOR | ROLE | PROBABILITY | SCORE | MACS.
        parent_candidates={m for m in (parent_mac,parent_bssid) if MAC_FULL.match(m)}
        try:
            for iid in self.lan_vendor_tree.get_children(""):
                vals=list(self.lan_vendor_tree.item(iid,"values") or ())
                if len(vals) < 5:
                    continue
                raw=str(vals[4] or "").replace("(*)","").strip().lower()
                if raw not in parent_candidates:
                    continue
                role=str(vals[1] or "").strip()
                if "(*)" not in role:
                    vals[1]=(role+" (*)").strip()
                self.lan_vendor_tree.item(iid,values=tuple(vals))
        except Exception:
            pass

        camdesc=", ".join(
            f"{m.upper()} [{i.get('provenance','')} (*)]" for m,i in allcams.items()
        )
        for pmac in parent_candidates:
            det=self.lan_candidate_details.setdefault(pmac,{})
            marker=("=== SECOND-SCAN CAMERA ASSOCIATION ==="
                    if is_en else "=== ASSOCIAZIONE TELECAMERA - SECONDA SCANSIONE ===")
            extra=str(det.get("details_extra","") or "")
            if marker not in extra:
                lines=[
                    marker,
                    ("Router marked (*) because cameras were detected in REAL TIME "
                     "during the second passive scan on its correlated BSSID."
                     if is_en else
                     "Router marcato (*) perche' durante la seconda scansione passiva "
                     "sul BSSID correlato sono state rilevate telecamere IN TEMPO REALE."),
                    f"BSSID: {parent_bssid or '-'}",
                    ("Associated cameras: " if is_en else "Telecamere associate: ")+camdesc,
                    ("The (*) is the visual link with LAN (*) / WIFI (*) in the camera table."
                     if is_en else
                     "L'asterisco (*) e' il collegamento visivo con LAN (*) / WIFI (*) nella tabella telecamere.")
                ]
                det["details_extra"]=extra+("\n\n" if extra else "")+"\n".join(lines)
            try:
                self.lan_persistent_details[pmac]=det
            except Exception:
                pass

        # Il placeholder è ormai definitivamente sostituito per questa seconda scansione.
        self._cascade_router_cam_placeholders=set()
        try:
            self._refresh_result_counters()
            self._refresh_camera_block_action()
        except Exception:
            pass


    def _cascade_second_scan_collect_links(self, rows):
        """Nuovo algoritmo separato: registra i dispositivi camera trovati nella seconda scansione."""
        if not getattr(self, "_cascade_second_scan_running", False):
            return
        match = getattr(self, "_cascade_pending_match", {}) or {}
        parent_mac = str(match.get("wan_mac", "") or "").lower()
        parent_bssid = str(match.get("bssid", "") or getattr(
            self, "_cascade_second_scan_target_bssid", ""
        ) or "").lower()

        if not hasattr(self, "_cascade_second_scan_cameras"):
            self._cascade_second_scan_cameras = {}

        placeholders = set(getattr(self, "_cascade_router_cam_placeholders", set()) or set())
        for row in rows or []:
            if not row:
                continue
            try:
                mac = str(row[0]).replace("(*)","").strip().lower()
            except Exception:
                continue
            if (not MAC_FULL.match(mac) or mac in placeholders
                    or mac in set(self._known_ap_bssids())):
                continue
            det = (getattr(self, "camera_candidate_details", {}) or {}).get(mac, {}) or {}
            if det.get("nvr_candidate") or det.get("cascade_camera_candidate"):
                continue

            # Provenienza reale prodotta dal normale motore camera.
            prov = ""
            try:
                prov = str(row[5] if len(row) > 5 else "").strip().upper()
            except Exception:
                pass
            dprov = str(det.get("provenance","") or "").strip().upper()
            if dprov in ("LAN","WIFI","WI-FI"):
                prov = dprov
            if prov in ("WI-FI","WIFI"):
                prov = "WIFI"
            elif prov == "LAN":
                prov = "LAN"
            else:
                # Non inventare la provenienza se il motore normale non l'ha stabilita.
                continue

            self._cascade_second_scan_cameras[mac] = {
                "provenance": prov,
                "parent_mac": parent_mac,
                "parent_bssid": parent_bssid,
                "row": tuple(row),
            }


    def _cascade_second_scan_finalize_association(self, rows):
        """Integra la seconda scansione senza alterare gli algoritmi di rilevamento."""
        self._cascade_second_scan_collect_links(rows)

        cams = dict(getattr(self, "_cascade_second_scan_cameras", {}) or {})
        if not cams:
            # Nessuna camera trovata: CAM DIETRO ROUTER resta visibile.
            self._merge_camera_candidate_rows(rows)
            return

        match = getattr(self, "_cascade_pending_match", {}) or {}
        parent_mac = str(match.get("wan_mac","") or "").lower()
        parent_bssid = str(match.get("bssid","") or getattr(
            self, "_cascade_second_scan_target_bssid", ""
        ) or "").lower()
        corr_score = match.get("score","")
        corr_ch = str(match.get("channel","") or "")
        corr_ssid = str(match.get("ssid","") or "")
        corr_reasons = match.get("reasons",[]) or []

        # Elimina esclusivamente il placeholder CAM DIETRO ROUTER della prima scansione.
        placeholders = set(getattr(self, "_cascade_router_cam_placeholders", set()) or set())
        for pmac in placeholders:
            self.camera_candidate_rows.pop(pmac, None)
            self.camera_candidate_details.pop(pmac, None)
            try:
                if self.camera_tree.exists(pmac):
                    self.camera_tree.delete(pmac)
            except Exception:
                pass
            try:
                for iid in self.camera_tree.get_children(""):
                    vals = self.camera_tree.item(iid,"values") or ()
                    if vals and str(vals[0]).replace("(*)","").strip().lower() == pmac:
                        self.camera_tree.delete(iid)
            except Exception:
                pass

        # Inserisce le telecamere reali usando MAC/vendor propri.
        final_rows = []
        for row in rows or []:
            if not row:
                continue
            mac = str(row[0]).replace("(*)","").strip().lower()
            if mac in placeholders:
                continue
            if mac not in cams:
                final_rows.append(row)
                continue

            info = cams[mac]
            prov = info["provenance"]
            rr = list(row)
            if len(rr) >= 6:
                rr[5] = prov + " (*)"

            # Vendor reale della camera.
            try:
                vendor = str(self.resolve_mac_with_manuf(mac) or "").strip()
            except Exception:
                vendor = ""
            if vendor and len(rr) > 1:
                rr[1] = vendor
            rr[0] = mac.upper()
            final_rows.append(tuple(rr))

            det = self.camera_candidate_details.setdefault(mac,{})
            det["provenance"] = prov
            det["source_display"] = prov + " (*)"
            det["second_scan_camera"] = True
            det["router_cam_parent_mac"] = parent_mac
            det["router_cam_parent_bssid"] = parent_bssid
            det["cascade_parent_bssid"] = parent_bssid

            is_en = getattr(self,"language","it") == "en"
            lines = [
                "=== SECOND-SCAN ROUTER ASSOCIATION ===" if is_en
                else "=== ASSOCIAZIONE ROUTER - SECONDA SCANSIONE ===",
                ("Camera detected during the SECOND passive scan."
                 if is_en else
                 "Telecamera rilevata durante la SECONDA scansione passiva."),
                (f"Associated router LAN/WAN MAC: {parent_mac or '-'}"
                 if is_en else
                 f"MAC LAN/WAN router associato: {parent_mac or '-'}"),
                f"BSSID: {parent_bssid or '-'}",
                f"SSID: {corr_ssid or '-'}",
                ("Channel: " if is_en else "Canale: ") + (corr_ch or "-"),
                ("Camera source: " if is_en else "Provenienza telecamera: ") + prov,
                ("Router/BSSID correlation: " if is_en else "Correlazione router/BSSID: ")
                    + ((str(corr_score)+"/100") if corr_score != "" else "-"),
            ]
            if corr_reasons:
                lines.append(
                    ("Correlation evidence: " if is_en else "Evidenze correlazione: ")
                    + ", ".join(map(str,corr_reasons))
                )
            oldextra = str(det.get("details_extra","") or "").strip()
            extra = "\n".join(lines)
            det["details_extra"] = oldextra + ("\n\n" if oldextra else "") + extra

        self._merge_camera_candidate_rows(final_rows)

        # Dopo il merge marca graficamente la provenienza LAN/WIFI con (*).
        for mac, info in cams.items():
            try:
                for iid in self.camera_tree.get_children(""):
                    vals = list(self.camera_tree.item(iid,"values") or ())
                    if not vals:
                        continue
                    raw = str(vals[0]).replace("(*)","").strip().lower()
                    if raw != mac:
                        continue
                    vals[0] = mac.upper()
                    if len(vals) > 5:
                        vals[5] = info["provenance"] + " (*)"
                    try:
                        vendor = str(self.resolve_mac_with_manuf(mac) or "").strip()
                    except Exception:
                        vendor = ""
                    if vendor and len(vals)>1:
                        vals[1]=vendor
                    self.camera_tree.item(iid,values=tuple(vals))
            except Exception:
                pass

        # Marca (*) sulla riga LAN del router associato e arricchisce i suoi dettagli.
        parent_candidates = {m for m in (parent_mac,parent_bssid) if MAC_FULL.match(m)}
        try:
            for iid in self.lan_tree.get_children(""):
                vals=list(self.lan_tree.item(iid,"values") or ())
                if not vals: continue
                raw=str(vals[0]).replace("(*)","").strip().lower()
                if raw not in parent_candidates: continue
                vals[0]=raw.upper()+" (*)"
                self.lan_tree.item(iid,values=tuple(vals))
        except Exception:
            pass

        camera_desc = ", ".join(
            f"{m.upper()} [{info['provenance']}]" for m,info in cams.items()
        )
        for pmac in parent_candidates:
            det = self.lan_candidate_details.setdefault(
                pmac,
                (getattr(self,"lan_persistent_details",{}) or {}).get(pmac,{}) or {}
            )
            is_en = getattr(self,"language","it") == "en"
            lines = [
                "=== SECOND-SCAN CAMERA ASSOCIATION ===" if is_en
                else "=== ASSOCIAZIONE TELECAMERE - SECONDA SCANSIONE ===",
                ("This router is marked (*) because one or more cameras were found "
                 "during the second passive scan on its correlated BSSID."
                 if is_en else
                 "Questo router e' marcato (*) perche' una o piu' telecamere sono state "
                 "trovate durante la seconda scansione passiva sul BSSID correlato."),
                f"BSSID: {parent_bssid or '-'}",
                ("Associated cameras: " if is_en else "Telecamere associate: ") + camera_desc,
            ]
            oldextra=str(det.get("details_extra","") or "").strip()
            extra="\n".join(lines)
            det["details_extra"]=oldextra+("\n\n" if oldextra else "")+extra
            try:
                self.lan_persistent_details[pmac]=det
            except Exception:
                pass

        self._cascade_router_cam_placeholders=set()


    def _apply_router_cam_link_annotations(self):
        """Algoritmo separato di sola annotazione GUI, senza toccare i motori di rilevamento."""
        try:
            if not getattr(self, "_cascade_second_scan_target_bssid", ""):
                return

            linked_cams = []
            for mac, det in (getattr(self, "camera_candidate_details", {}) or {}).items():
                det = det or {}
                if det.get("router_cam_confirmed"):
                    linked_cams.append(str(mac).lower())

            if not linked_cams:
                return

            match = getattr(self, "_cascade_pending_match", {}) or {}
            parent_mac = str(match.get("wan_mac", "") or "").lower()
            parent_bssid = str(match.get("bssid", "") or getattr(
                self, "_cascade_second_scan_target_bssid", ""
            ) or "").lower()

            # POSSIBILI TELECAMERE: MAC reale camera + (*) e vendor reale.
            try:
                for cam_mac in linked_cams:
                    for iid in self.camera_tree.get_children(""):
                        vals = list(self.camera_tree.item(iid, "values") or ())
                        if not vals:
                            continue
                        raw = str(vals[0] or "").replace("(*)","").strip().lower()
                        if raw != cam_mac:
                            continue
                        vals[0] = cam_mac.upper() + " (*)"
                        try:
                            vendor = str(self.resolve_mac_with_manuf(cam_mac) or "").strip()
                        except Exception:
                            vendor = ""
                        if vendor and len(vals) > 1:
                            vals[1] = vendor
                        self.camera_tree.item(iid, values=tuple(vals))
            except Exception:
                pass

            # LAN: marca con (*) la colonna RUOLO/ROLE del router collegato.
            parent_candidates = [m for m in (parent_mac, parent_bssid) if MAC_FULL.match(m)]
            try:
                for iid in self.lan_vendor_tree.get_children(""):
                    vals = list(self.lan_vendor_tree.item(iid, "values") or ())
                    if len(vals) < 5:
                        continue
                    raw = str(vals[4] or "").replace("(*)","").strip().lower()
                    if raw not in parent_candidates:
                        continue
                    role = str(vals[1] or "").strip()
                    if "(*)" not in role:
                        vals[1] = (role + " (*)").strip()
                    self.lan_vendor_tree.item(iid, values=tuple(vals))
            except Exception:
                pass

            for cam_mac in linked_cams:
                det = self.camera_candidate_details.setdefault(cam_mac, {})
                det["router_cam_link_marked"] = True
                det["router_cam_parent_mac"] = parent_mac
                det["router_cam_parent_bssid"] = parent_bssid

            self._router_cam_link_parent_mac = parent_mac
            self._router_cam_link_parent_bssid = parent_bssid
            self._router_cam_link_camera_macs = set(linked_cams)

        except Exception as e:
            try:
                self.logmsg(f"ROUTER-CAM link annotation: {e}")
            except Exception:
                pass


    def _merge_camera_candidate_rows_cascade_final(self, rows):
        """Merge finale della seconda scansione router-cascata.

        Mantiene visibili i risultati della prima scansione durante tutta la
        seconda cattura e soltanto alla fine sostituisce la riga
        CAM DIETRO ROUTER con la/le telecamere realmente trovate sul BSSID
        correlato, marcandole ROUTER-CAM.
        """
        self._cascade_router_cam_finalize_merge = True
        try:
            # Ripristina in memoria i risultati della prima scansione SOLO ORA,
            # a seconda cattura conclusa. Durante l'analisi live le cache erano
            # volutamente vuote per replicare una scansione manuale indipendente.
            try:
                for _m, _r in (getattr(self, "_cascade_first_camera_rows", {}) or {}).items():
                    self.camera_candidate_rows.setdefault(str(_m).lower(), _r)
                for _m, _d in (getattr(self, "_cascade_first_camera_details", {}) or {}).items():
                    self.camera_candidate_details.setdefault(str(_m).lower(), _d)
            except Exception:
                pass

            self._cascade_second_scan_finalize_association(rows)
        finally:
            self._cascade_router_cam_finalize_merge = False
            self._cascade_second_scan_running = False
            try:
                self._refresh_result_counters()
                self._refresh_camera_block_action()
                self.root.update_idletasks()
            except Exception:
                pass
        try:
            self._network_graph_snapshot_current(
                getattr(self, "_cascade_second_scan_target_bssid", "") or None,
                "cascade final camera analysis"
            )
        except Exception:
            pass


    def _camera_capture_is_complete(self):
        """True soltanto quando la cattura manuale ha raggiunto realmente il 100%."""
        try:
            return float(self.progress_value.get()) >= 99.5 and self.capture_process is None
        except Exception:
            return False

    @staticmethod
    def _camera_fmt_bytes(value):
        try:
            value=float(value)
        except Exception:
            return "0 B"
        for unit in ("B","KB","MB","GB"):
            if value < 1024.0 or unit == "GB":
                return f"{value:.1f} {unit}"
            value /= 1024.0
        return f"{value:.1f} GB"



    def _wifi_client_macs(self):
        """MAC attualmente presenti nella tabella dei client Wi-Fi rilevati."""
        found=set()
        try:
            for item in self.client_tree.get_children():
                vals=self.client_tree.item(item,"values")
                if not vals:
                    continue
                mac=str(vals[0]).strip().lower()
                if MAC_FULL.match(mac):
                    found.add(mac)
        except Exception:
            pass
        return found


    def _refresh_camera_block_button_theme(self):
        """Aggiorna il pulsante BLOCCA/BLOCK in base al tema."""
        buttons = [
            getattr(self, "camera_block_action_button", None),
            getattr(self, "camera_details_button", None),
        ]
        buttons = [b for b in buttons if b is not None]
        if not buttons:
            return
        try:
            if getattr(self,"night_mode",False):
                for btn in buttons:
                    btn.configure(
                    bg="#4A4F54",
                    fg="#E8E8E8",
                    activebackground="#62686E",
                    activeforeground="#FFFFFF",
                    disabledforeground="#8A8F94"
                    )
            else:
                for btn in buttons:
                    btn.configure(
                    bg="#D9D9D9",
                    fg="#202020",
                    activebackground="#BDBDBD",
                    activeforeground="#000000",
                    disabledforeground="#888888"
                    )
        except Exception:
            pass

    def _hide_camera_block_delay_notice(self):
        """Nasconde l'avviso temporaneo sopra il riquadro BLOCCO."""
        notice = getattr(self, "camera_block_delay_notice", None)
        if notice is not None:
            try:
                notice.destroy()
            except Exception:
                pass
        self.camera_block_delay_notice = None

    def _show_camera_block_delay_notice(self, provenance):
        """Mostra l'avviso sopra BLOCCO finché non viene premuto uno dei due AVVIA."""
        self._hide_camera_block_delay_notice()
        panel = getattr(self, "block_panel", None)
        if panel is None:
            return
        is_en = getattr(self, "language", "it") == "en"
        prov = str(provenance or "").strip().upper().replace("-", "")
        if prov == "WIFI":
            text = "BLOCK ACTIVE AFTER 30 SECONDS" if is_en else "BLOCCO ATTIVO DOPO 30 SECONDI"
        elif prov == "LAN":
            text = "BLOCK NOT GUARANTEED" if is_en else "BLOCCO NON GARANTITO"
        else:
            return
        try:
            dark = bool(getattr(self, "night_mode", False))

            # Overlay sulla GUI principale: non altera la geometria di BLOCCO.
            notice = tk.Label(
                self.root, text=text,
                font=("TkDefaultFont", 9, "bold"),
                bg=("#332A12" if dark else "#FFF3CD"),
                fg=("#E7D9A5" if dark else "#6B4F00"),
                relief="solid", bd=1,
                highlightthickness=2,
                highlightbackground=("#FFFFFF" if dark else "#000000"),
                highlightcolor=("#FFFFFF" if dark else "#000000"),
                padx=7, pady=4,
                justify="center", anchor="center"
            )
            self.camera_block_delay_notice = notice

            # LAN: riga ROUTER. WIFI: riga CLIENT.
            stop_btn = (
                getattr(self, "aireplay_ng_client_stop_button", None)
                if prov == "WIFI"
                else getattr(self, "aireplay_ng_router_stop_button", None)
            )
            if stop_btn is None:
                notice.destroy()
                self.camera_block_delay_notice = None
                return

            self.root.update_idletasks()

            # A destra di FERMA, lasciando uno spazio visibile.
            gap = 22
            root_x = int(self.root.winfo_rootx())
            root_y = int(self.root.winfo_rooty())
            x = int(stop_btn.winfo_rootx() - root_x + stop_btn.winfo_width() + gap)
            y_center = int(
                stop_btn.winfo_rooty() - root_y + (stop_btn.winfo_height() / 2)
            )

            notice.place(x=x, y=y_center, anchor="w")
            notice.lift()
        except Exception:
            try:
                notice.destroy()
            except Exception:
                pass
            self.camera_block_delay_notice = None

    def _selected_camera_mac(self):
        """Restituisce il MAC della riga telecamera selezionata."""
        try:
            sel=self.camera_tree.selection()
            if not sel:
                return ""
            vals=self.camera_tree.item(sel[0],"values")
            if not vals:
                return ""
            mac=str(vals[0]).strip().lower()
            return mac if MAC_FULL.match(mac) else ""
        except Exception:
            return ""

    def _refresh_camera_block_action(self):
        """Abilita BLOCCA DISPOSITIVO SELEZIONATO per ogni telecamera valida selezionata.

        - LAN: il MAC verra' inviato al campo BLOCCO ROUTER.
        - WIFI: il MAC verra' inviato al campo BLOCCO CLIENT.
        La presenza contemporanea nella tabella CLIENT non e' piu' richiesta:
        se la telecamera e' gia' stata riconosciuta dalla sezione TELECAMERE,
        la selezione della sua riga e' sufficiente ad abilitare il pulsante.
        """
        try:
            btn = getattr(self, "camera_block_action_button", None)
            tree = getattr(self, "camera_tree", None)
            if btn is None or tree is None:
                return

            sel = tree.selection()
            if not sel:
                btn.configure(state="disabled")
                return

            vals = tree.item(sel[0], "values")
            if not vals:
                btn.configure(state="disabled")
                return

            mac = str(vals[0]).strip().lower()
            if not MAC_FULL.match(mac):
                btn.configure(state="disabled")
                return

            # Una riga telecamera valida e selezionata e' sempre bloccabile,
            # sia che provenga da WIFI sia che provenga da LAN.
            btn.configure(state="normal")
        except Exception:
            try:
                self.camera_block_action_button.configure(state="disabled")
            except Exception:
                pass

    def _camera_block_selected_client(self):
        """Invia la selezione telecamera al riquadro BLOCCO corretto.

        WIFI -> MAC telecamera nel campo CLIENT.
        LAN  -> BSSID/router selezionato all'inizio nel campo ROUTER.
        """
        try:
            tree = getattr(self, "camera_tree", None)
            if tree is None:
                return
            sel = tree.selection()
            if not sel:
                return
            vals = tree.item(sel[0], "values")
            if not vals or len(vals) < 6:
                return

            camera_mac = str(vals[0]).strip().lower()
            provenance = str(vals[5]).strip().upper().replace("-", "")
            if not MAC_FULL.match(camera_mac):
                return

            # Se la provenienza non è leggibile dalla riga, usa i dettagli salvati.
            if provenance not in ("WIFI", "LAN"):
                det = (getattr(self, "camera_candidate_details", {}) or {}).get(camera_mac, {}) or {}
                provenance = str(det.get("provenance", "")).strip().upper().replace("-", "")

            if provenance == "WIFI":
                # Telecamera Wi-Fi: si agisce sul client radio specifico.
                self.block_client_value.set(camera_mac)
                self._show_camera_block_delay_notice("WIFI")
                try:
                    self.set_status('Wi-Fi camera copied to CLIENT BLOCK: ' + camera_mac)
                except Exception:
                    pass

            elif provenance == "LAN":
                # Telecamera LAN: non usare il MAC della telecamera.
                # Il BLOCCO ROUTER deve contenere il router/BSSID scelto all'inizio.
                router_mac = str(self.bssid.get() or "").strip().lower()
                if not MAC_FULL.match(router_mac):
                    try:
                        messagebox.showwarning(
                            "WARNING" if getattr(self, "language", "it") == "en" else "AVVISO",
                            "Select the router first." if getattr(self, "language", "it") == "en"
                            else "Seleziona prima il router."
                        )
                    except Exception:
                        pass
                    return
                self.block_router_value.set(router_mac)
                self._show_camera_block_delay_notice("LAN")
                try:
                    self.set_status(
                        ('LAN camera: selected router copied to ROUTER BLOCK: ' if getattr(self, "language", "it") == "en"
                         else 'Telecamera LAN: router selezionato copiato in BLOCCO ROUTER: ') + router_mac
                    )
                except Exception:
                    pass
            else:
                return

            try:
                self._refresh_camera_block_action()
            except Exception:
                pass
        except Exception:
            pass

    def _camera_selection_changed(self):
        """Aggiorna immediatamente i pulsanti DETTAGLI e BLOCCA alla selezione."""
        try:
            tree = getattr(self, "camera_tree", None)
            selected = bool(tree is not None and tree.selection())
        except Exception:
            selected = False

        try:
            details_btn = getattr(self, "camera_details_button", None)
            if details_btn is not None:
                details_btn.configure(state=("normal" if selected else "disabled"))
        except Exception:
            pass

        try:
            if selected:
                self._refresh_camera_block_action()
            else:
                block_btn = getattr(self, "camera_block_action_button", None)
                if block_btn is not None:
                    block_btn.configure(state="disabled")
        except Exception:
            pass

    def _on_camera_row_click(self, event=None):
        """Seleziona il candidato e apre subito i dettagli della riga scelta."""
        if not hasattr(self, "camera_tree"):
            return
        try:
            rowid = self.camera_tree.identify_row(event.y) if event is not None else ""
        except Exception:
            rowid = ""
        if not rowid:
            sel = self.camera_tree.selection()
            rowid = sel[0] if sel else ""
        if not rowid:
            return
        try:
            self.camera_tree.selection_set(rowid)
            self.camera_tree.focus(rowid)
        except Exception:
            pass

        # Selezionando una telecamera valida si attivano ENTRAMBI i pulsanti.
        # Le azioni vengono eseguite solo quando l'utente preme il relativo pulsante.
        try:
            btn = getattr(self, "camera_details_button", None)
            if btn is not None:
                btn.configure(state="normal")
        except Exception:
            pass

        try:
            self._refresh_camera_block_action()
        except Exception:
            pass

    def _camera_show_selected_detail(self):
        """Mostra i dettagli completi della riga selezionata nella tabella telecamere."""
        if not hasattr(self, "camera_tree"):
            return
        try:
            sel = self.camera_tree.selection()
            rowid = sel[0] if sel else self.camera_tree.focus()
        except Exception:
            rowid = ""
        if not rowid:
            messagebox.showinfo(
                "Dettagli telecamera",
                "Seleziona prima un dispositivo nella tabella POSSIBILI TELECAMERE RILEVATE."
            )
            return
        self._show_camera_detail(rowid)


    def _enable_detail_text_copy(self, text_widget):
        """Abilita copia da tastiera e menu contestuale nei riquadri DETTAGLI."""
        is_en = getattr(self, "language", "it") == "en"

        def copy_selection(_event=None):
            try:
                selected = text_widget.get("sel.first", "sel.last")
            except Exception:
                return "break"
            try:
                self.root.clipboard_clear()
                self.root.clipboard_append(selected)
                self.root.update_idletasks()
            except Exception:
                pass
            return "break"

        def select_all(_event=None):
            try:
                # La selezione resta disponibile anche se il Text è readonly.
                text_widget.tag_add("sel", "1.0", "end-1c")
                text_widget.mark_set("insert", "1.0")
                text_widget.see("1.0")
            except Exception:
                pass
            return "break"

        menu = tk.Menu(text_widget, tearoff=0)
        menu.add_command(
            label=("COPY" if is_en else "COPIA"),
            command=copy_selection
        )
        menu.add_command(
            label=("SELECT ALL" if is_en else "SELEZIONA TUTTO"),
            command=select_all
        )

        def popup_menu(event):
            try:
                text_widget.focus_set()
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                try:
                    menu.grab_release()
                except Exception:
                    pass
            return "break"

        text_widget.bind("<Control-c>", copy_selection)
        text_widget.bind("<Control-C>", copy_selection)
        text_widget.bind("<Control-a>", select_all)
        text_widget.bind("<Control-A>", select_all)
        text_widget.bind("<Button-3>", popup_menu)

        # Su alcuni touchpad/Linux il menu contestuale arriva come Button-2.
        text_widget.bind("<Button-2>", popup_menu)

    def _show_camera_detail(self, mac):
        mac=str(mac or "").lower()
        detail=(getattr(self,"camera_candidate_details",{}) or {}).get(mac)
        is_en=getattr(self,"language","it")=="en"

        # Fallback ai dati visibili della riga, se il dettaglio completo non è disponibile.
        if not detail and hasattr(self,"camera_tree"):
            try:
                for item in self.camera_tree.get_children():
                    vals=self.camera_tree.item(item,"values")
                    if vals and str(vals[0]).lower()==mac:
                        score_text=str(vals[2]) if len(vals)>2 else "0/100"
                        mm=re.search(r"(\d{1,3})",score_text)
                        score=int(mm.group(1)) if mm else 0
                        detail={
                            "mac":mac,
                            "vendor":str(vals[1]) if len(vals)>1 else ("Unknown" if is_en else "Unknown"),
                            "score":score,
                            "level":str(vals[3]) if len(vals)>3 else "",
                            "txrx":str(vals[4]) if len(vals)>4 else "--",
                            "provenance":str(vals[5]) if len(vals)>5 else "--",
                            "bitrate":"--",
                            "duration":str(vals[6]) if len(vals)>6 else "--",
                            "reasons":[],
                            "score_parts":{},
                        }
                        break
            except Exception:
                pass

        if not detail:
            messagebox.showinfo(
                "Camera analysis" if is_en else "Dettagli telecamera",
                "Detailed analysis is not available for this device." if is_en
                else "Detailed analysis is not available for this device."
            )
            return

        title="CAMERA TRAFFIC ANALYSIS" if is_en else "ANALISI DISPOSITIVO TELECAMERA"
        win=self._create_inapp_detail_popup(title,760,640)
        self.camera_detail_window=win

        # SCORE / LIVELLO
        try:
            raw_score=detail.get("score",0)
            if isinstance(raw_score,str):
                mm=re.search(r"(\d{1,3})",raw_score)
                score=int(mm.group(1)) if mm else 0
            else:
                score=int(raw_score)
        except Exception:
            score=0

        level=str(detail.get("level","") or "")
        if not level:
            if is_en:
                level="HIGHLY LIKELY" if score>=80 else "LIKELY" if score>=62 else "POSSIBLE" if score>=42 else "LOW CONFIDENCE"
            else:
                level="MOLTO PROBABILE" if score>=80 else "PROBABILE" if score>=62 else "POSSIBILE" if score>=42 else "DA OSSERVARE"

        # Layout IDENTICO alla LAN: score panel sopra, area testo sotto.
        self._build_score_panel(win,score,level,kind="CAMERA")

        def val(*keys, default="--"):
            for k in keys:
                try:
                    v=detail.get(k,None)
                except Exception:
                    v=None
                if v not in (None,""):
                    return v
            return default

        # Tutti i dati dettagliati della versione precedente.
        mac_v=val("mac",default=mac)
        vendor=val("vendor",default=("Unknown" if is_en else "Unknown"))

        # WIFI_435: nei dettagli mostra il RISULTATO REALE della PROVENIENZA
        # visualizzato nella tabella telecamere, non solo la classe generica WIFI/LAN.
        provenance = ""
        try:
            for _iid in self.camera_tree.get_children(""):
                _vals = tuple(self.camera_tree.item(_iid, "values") or ())
                if not _vals:
                    continue
                _row_mac = str(_vals[0] or "").replace("(*)", "").strip().lower()
                if _row_mac == mac and len(_vals) > 5:
                    provenance = str(_vals[5] or "").strip()
                    break
        except Exception:
            provenance = ""

        if not provenance:
            provenance = str(
                val(
                    "source_display",
                    "source_label",
                    "provenance",
                    default=("WIFI" if str(val("class",default="")).upper().startswith("WI-FI") else "--")
                )
                or "--"
            ).strip()

        txrx=val("txrx")
        bitrate=val("bitrate")
        tx_bitrate=val("tx_bitrate","txbitrate")
        duration=val("duration")
        frames=val("frames","frame_count")
        tx_bytes=val("tx_bytes","tx")
        rx_bytes=val("rx_bytes","rx")
        tx_ratio=val("tx_ratio")
        activity=val("activity_ratio","activity")
        tx_activity=val("tx_activity")
        avg_size=val("avg_frame_size","mean_frame_size","avg_size")
        inter_arrival=val("mean_iat","inter_arrival","iat")
        burst_cv=val("burst_cv")
        retry_ratio=val("retry_ratio")
        signal=val("avg_signal","signal","rssi")
        p95=val("p95_rate")
        p95_tx=val("p95_tx_rate")
        large_ratio=val("large_ratio")
        small_ratio=val("small_ratio")
        presence=val("presence","presence_ratio")
        continuity=val("continuity","continuity_score")
        regularity=val("regularity")
        notes=str(val("notes",default="") or "").strip()

        reasons=list(detail.get("reasons",[]) or [])
        score_parts=detail.get("score_parts",{}) or {}
        if not isinstance(score_parts,dict):
            score_parts={}

        if is_en:
            lines=[
                "IDENTITY",
                f"MAC: {mac_v}",
                f"VENDOR: {vendor}",
                f"SOURCE RESULT: {provenance}",
                "",
                "OBSERVED TRAFFIC",
                f"TX/RX: {txrx}",
                f"TOTAL BITRATE: {bitrate}",
                f"TX BITRATE: {tx_bitrate}",
                f"DURATION: {duration}",
                f"FRAMES: {frames}",
                f"TX BYTES: {tx_bytes}",
                f"RX BYTES: {rx_bytes}",
                f"TX RATIO: {tx_ratio}",
                "",
                "TRAFFIC BEHAVIOR",
                f"ACTIVITY: {activity}",
                f"TX ACTIVITY: {tx_activity}",
                f"MEAN FRAME SIZE: {avg_size}",
                f"MEAN MEAN INTER-ARRIVAL TIME TIME: {inter_arrival}",
                f"TRAFFIC VARIABILITY (CV): {burst_cv}",
                f"802.11 802.11 RETRY RATIO: {retry_ratio}",
                f"MEAN RSSI: {signal}",
                f"95TH-PERCENTILE BITRATE: {p95}",
                f"95TH-PERCENTILE TX BITRATE: {p95_tx}",
                f"LARGE-FRAME RATIO: {large_ratio}",
                f"SMALL-FRAME RATIO: {small_ratio}",
                f"OBSERVED PRESENCE: {presence}",
                f"TRAFFIC CONTINUITY: {continuity}",
                f"TEMPORAL REGULARITY: {regularity}",
                "",
                "SCORE BREAKDOWN",
            ]
        else:
            lines=[
                "IDENTITA'",
                f"MAC: {mac_v}",
                f"VENDITORE: {vendor}",
                f"RISULTATO PROVENIENZA: {provenance}",
                "",
                "TRAFFICO",
                f"TX/RX: {txrx}",
                f"BITRATE TOTALE: {bitrate}",
                f"BITRATE TX: {tx_bitrate}",
                f"DURATA: {duration}",
                f"FRAME: {frames}",
                f"BYTE TX: {tx_bytes}",
                f"BYTE RX: {rx_bytes}",
                f"RAPPORTO TX: {tx_ratio}",
                "",
                "COMPORTAMENTO",
                f"ATTIVITA': {activity}",
                f"ATTIVITA' TX: {tx_activity}",
                f"DIMENSIONE MEDIA FRAME: {avg_size}",
                f"MEAN MEAN INTER-ARRIVAL TIME TIME: {inter_arrival}",
                f"TRAFFIC VARIABILITY (CV): {burst_cv}",
                f"RAPPORTO RETRY: {retry_ratio}",
                f"SEGNALE MEDIO: {signal}",
                f"P95 BITRATE: {p95}",
                f"P95 TX: {p95_tx}",
                f"QUOTA FRAME GRANDI: {large_ratio}",
                f"QUOTA FRAME PICCOLI: {small_ratio}",
                f"PRESENZA: {presence}",
                f"CONTINUITA': {continuity}",
                f"REGOLARITA': {regularity}",
                "",
                "COMPOSIZIONE SCORE",
            ]

        if score_parts:
            labels_en={
                "identity":"Vendor / OUI Evidence",
                "direction":"TX/RX Directionality",
                "continuity":"Traffic Continuity",
                "shape":"Frame-size / traffic-shape pattern",
                "temporal":"Temporal pattern",
                "radio":"RF Signal Stability",
                "presence":"Observed Presence",
                "penalty":"False-positive penalties",
                "uncertainty_penalty":"Uncertainty penalty",
            }
            labels_it={
                "identity":"Identità/vendor",
                "direction":"Direzione TX",
                "continuity":"Continuità",
                "shape":"Forma traffico",
                "temporal":"Temporizzazione",
                "radio":"Stabilità radio",
                "presence":"Presenza",
                "penalty":"Penalità",
                "uncertainty_penalty":"Penalità incertezza",
            }
            labels=labels_en if is_en else labels_it
            for k,v in score_parts.items():
                label=labels.get(str(k),str(k))
                try:
                    num=float(v)
                    sign="+" if num>0 else ""
                    if num.is_integer():
                        sval=f"{sign}{int(num)}"
                    else:
                        sval=f"{sign}{num:.1f}"
                except Exception:
                    sval=str(v)
                lines.append(f"{label}: {sval}")
        else:
            lines.append(
                "Detailed score components not available." if is_en
                else "Componenti dettagliati dello score non disponibili."
            )

        lines += [
            "",
            "CLASSIFICATION RATIONALE" if is_en else "MOTIVAZIONI DEL RILEVAMENTO",
        ]

        if reasons:
            for reason in reasons:
                lines.append("• "+str(reason))
        else:
            lines.append(
                "• Traffic behaviour compatible with an always-on camera/IoT device."
                if is_en else
                "• Comportamento del traffico compatibile con telecamera/dispositivo IoT sempre attivo."
            )

        if notes:
            lines += [
                "",
                "ADDITIONAL NOTES" if is_en else "NOTE AGGIUNTIVE",
                notes
            ]

        lines += [
            "",
            "TECHNICAL NOTE" if is_en else "NOTA TECNICA",
            (
                "The classification is probabilistic and uses only characteristics observable from encrypted IEEE 802.11 traffic. "
                "IP addresses, transport-layer ports, and application-layer protocols are not used."
                if is_en else
                "La classificazione è probabilistica e usa esclusivamente caratteristiche osservabili del traffico Wi-Fi cifrato. "
                "Indirizzi IP, porte e protocolli applicativi non vengono utilizzati."
            )
        ]

        body_frame=tk.Frame(win,bd=0,highlightthickness=0)
        body_frame.pack(fill="both",expand=True,padx=10,pady=(10,5))
        body_frame.columnconfigure(0,weight=1)
        body_frame.rowconfigure(0,weight=1)

        body=tk.Text(
            body_frame,wrap="word",font=("TkDefaultFont",11),
            padx=16,pady=14,borderwidth=0
        )
        body.grid(row=0,column=0,sticky="nsew")

        body_y=ttk.Scrollbar(
            body_frame,orient="vertical",command=body.yview
        )
        body_y.grid(row=0,column=1,sticky="ns")
        body.configure(yscrollcommand=body_y.set)

        body.insert("1.0","\n".join(lines))
        body.configure(state="disabled")
        self._enable_detail_text_copy(body)

        # Nessun pulsante CHIUDI/CLOSE nel pannello dettagli telecamera.
        # Il pannello resta gestito dalla normale chiusura prevista dalla GUI.
        win.bind("<Escape>",lambda _e: win._close_popup())

        try:
            self._force_camera_detail_dark_theme(win)
            win.update_idletasks()
        except Exception:
            pass
        self._show_inapp_detail_popup(win)


    def open_camera_detail(self, mac):
        return self._show_camera_detail(mac)

    def show_camera_detail(self, mac):
        return self._show_camera_detail(mac)

    def open_camera_details(self, mac):
        return self._show_camera_detail(mac)


    def _analyze_lan_camera_candidates(self, cap, bssid):
        """
        Estende l'algoritmo telecamere agli endpoint lato LAN/Distribution System.

        Un dispositivo LAN viene ricavato dai frame DATA 802.11:
        - ToDS=1: wlan.da è la destinazione finale lato DS/LAN -> traffico RX del device LAN
        - FromDS=1: wlan.sa è la sorgente finale lato DS/LAN -> traffico TX del device LAN

        Lo score usa gli stessi segnali comportamentali principali del motore Wi-Fi:
        vendor/OUI, prevalenza TX, continuità, frame grandi, bitrate, regolarità e
        penalità anti-falso-positivo. Il vendor è soltanto un bonus: senza traffico
        DS/LAN osservato e comportamento compatibile il dispositivo viene escluso.
        Non usa il segnale RF, perché un endpoint LAN non è la station radio osservata direttamente.
        """
        is_en = getattr(self, "language", "it") == "en"
        if not cap or not Path(cap).exists():
            return []
        bssid = str(bssid or "").strip().lower()
        if not MAC_FULL.match(bssid):
            return []

        cmd = [
            "tshark", "-r", str(cap), "-T", "fields",
            "-E", "separator=/t", "-E", "occurrence=f",
            "-e", "frame.time_epoch", "-e", "frame.len",
            "-e", "wlan.fc.type", "-e", "wlan.fc.retry",
            "-e", "wlan.fc.tods", "-e", "wlan.fc.fromds",
            "-e", "wlan.sa", "-e", "wlan.da", "-e", "wlan.ta", "-e", "wlan.ra",
            "-e", "wlan.bssid"
        ]
        p = run(cmd, timeout=20)
        if p.returncode != 0 and not (p.stdout or "").strip():
            return []

        def _first_mac(v):
            m = MAC_FIND.search(v or "")
            return m.group(0).lower() if m else ""

        def _flag(v):
            s = str(v or "").strip().lower()
            if s in ("1", "true", "yes", "set"):
                return True
            if s in ("0", "false", "no", "not set", ""):
                return False
            try:
                return bool(int(float(s)))
            except Exception:
                return False

        def _int(v):
            try:
                return int(float(str(v or "0").split(",", 1)[0]))
            except Exception:
                return 0

        def _float(v):
            try:
                return float(str(v or "0").split(",", 1)[0])
            except Exception:
                return 0.0

        def _mean(vals):
            return sum(vals) / len(vals) if vals else 0.0

        def _cv(vals):
            if len(vals) < 2:
                return 99.0
            m = _mean(vals)
            if m <= 0:
                return 99.0
            return (sum((x-m)**2 for x in vals) / len(vals))**0.5 / m

        def _percentile(vals, pct):
            if not vals:
                return 0.0
            s = sorted(vals)
            pos = (len(s)-1) * pct
            lo = int(pos)
            hi = min(len(s)-1, lo+1)
            frac = pos-lo
            return s[lo]*(1-frac) + s[hi]*frac

        wifi_known = set(getattr(self, "wifi_radio_macs_session", set()) or set())
        wifi_known.update(getattr(self, "wifi_radio_macs_global", set()) or set())
        wifi_known.update(self._wifi_client_macs())
        related_radio_bssids=self._related_radio_bssids(bssid)
        wifi_known.update(related_radio_bssids)
        # Tutti i BSSID noti sono infrastruttura, non endpoint LAN/camere.
        infrastructure_bssids = set(self._known_ap_bssids())
        infrastructure_bssids.add(bssid)
        wifi_known.update(infrastructure_bssids)

        stats = {}
        cap_first = None
        cap_last = None

        def _get(mac):
            return stats.setdefault(mac, {
                "first": None, "last": None,
                "frames": 0, "data_frames": 0, "retry": 0,
                "tx_bytes": 0, "rx_bytes": 0,
                "tx_frames": 0, "rx_frames": 0,
                "lengths": [], "large": 0, "small": 0,
                "times": [], "tx_times": [],
                "seconds": {}, "tx_seconds": {}
            })

        def _add(mac, direction, ts, flen, retry):
            if (
                not mac or mac == bssid or not MAC_FULL.match(mac)
                or self.is_multicast_or_broadcast(mac) or mac in wifi_known
            ):
                return
            st = _get(mac)
            st["frames"] += 1
            st["data_frames"] += 1
            st["retry"] += 1 if retry else 0
            st["lengths"].append(flen)
            if flen >= 1000:
                st["large"] += 1
            elif flen <= 300:
                st["small"] += 1
            if direction == "tx":
                st["tx_bytes"] += flen
                st["tx_frames"] += 1
            else:
                st["rx_bytes"] += flen
                st["rx_frames"] += 1
            if ts > 0:
                st["times"].append(ts)
                st["first"] = ts if st["first"] is None else min(st["first"], ts)
                st["last"] = ts if st["last"] is None else max(st["last"], ts)
                sec = int(ts)
                st["seconds"][sec] = st["seconds"].get(sec, 0) + flen
                if direction == "tx":
                    st["tx_times"].append(ts)
                    st["tx_seconds"][sec] = st["tx_seconds"].get(sec, 0) + flen

        for line in (p.stdout or "").splitlines():
            f = line.split("\t")
            f += [""] * (11-len(f))
            ts, flen, ftype, retry, tods, fromds, sa, da, ta, ra, fb = f[:11]
            ts = _float(ts)
            flen = max(0, _int(flen))
            if ts > 0:
                cap_first = ts if cap_first is None else min(cap_first, ts)
                cap_last = ts if cap_last is None else max(cap_last, ts)

            if _int(ftype) != 2:
                continue
            sa_m, da_m = _first_mac(sa), _first_mac(da)
            ta_m, ra_m, fb_m = _first_mac(ta), _first_mac(ra), _first_mac(fb)
            if bssid not in (fb_m, ta_m, ra_m, sa_m, da_m):
                continue

            to_ds = _flag(tods)
            from_ds = _flag(fromds)
            is_retry = _flag(retry)

            if to_ds and not from_ds:
                # Station Wi-Fi -> AP -> endpoint LAN: il device LAN riceve.
                _add(da_m, "rx", ts, flen, is_retry)
            elif from_ds and not to_ds:
                # Endpoint LAN -> AP -> station Wi-Fi: il device LAN trasmette.
                _add(sa_m, "tx", ts, flen, is_retry)
            elif to_ds and from_ds:
                # WDS/bridge: sorgente e destinazione logiche possono essere endpoint DS.
                _add(sa_m, "tx", ts, flen, is_retry)
                _add(da_m, "rx", ts, flen, is_retry)

        camera_vendor_strong = (
            "hikvision","dahua","axis","vivotek","reolink","foscam","ezviz","imou",
            "arlo","wyze","ring","blink","amcrest","hanwha","wisenet","bosch security",
            "mobotix","avigilon","instar","lorex","swann","geovision","acti","xiongmai","xmeye"
        )
        camera_vendor_mixed = ("ubiquiti","unifi","tapo","tp-link","eufy")
        iot_vendor_words = ("tuya","espressif","realtek","ingenic","sonoff","silicon labs")
        consumer_vendor_words = (
            "apple","intel","lenovo","dell","hewlett","google","motorola","oneplus",
            "asustek","acer","microsoft"
        )

        # IMPORTANTE: il solo OUI/vendor NON dimostra che il dispositivo sia
        # una telecamera. Un produttore come Dahua può usare lo stesso blocco MAC
        # anche su NVR, DVR, citofoni, controller e altri apparati.
        # Per entrare tra le POSSIBILI TELECAMERE LAN il MAC deve quindi essere
        # realmente osservato nel PCAP come endpoint DS/LAN e mostrare indizi
        # comportamentali compatibili con traffico video.
        active_rows = getattr(self, "active_lan_results", {}) or {}

        out = []
        cache = load_vendor_cache()
        capture_duration = max(0.0, (cap_last or 0) - (cap_first or 0))

        for mac, st in stats.items():
            # Vendor: prima informazioni LAN già risolte, poi OUI locale.
            lan_det = (getattr(self, "lan_candidate_details", {}) or {}).get(mac, {}) or {}
            active_det = (active_rows.get(mac, {}) or {}).get("details", {}) or {}
            vendor = str(
                lan_det.get("vendor") or active_det.get("vendor") or cache.get(mac, "") or ""
            ).strip()
            if not vendor:
                resolved = self.resolve_mac_with_manuf(mac)
                if resolved not in ("Sconosciuto", "Unknown", "MAC locale/randomizzato"):
                    vendor = str(resolved).split("_", 1)[0]
            if not vendor:
                vendor = "Unknown" if is_en else "Sconosciuto"

            vlow = vendor.lower()
            duration = max(0.0, (st.get("last") or 0) - (st.get("first") or 0))
            tx = int(st.get("tx_bytes", 0))
            rx = int(st.get("rx_bytes", 0))
            total = max(1, tx + rx)
            tx_ratio = tx / total
            bitrate = (total * 8.0 / duration / 1_000_000.0) if duration >= 1 else 0.0
            tx_bitrate = (tx * 8.0 / duration / 1_000_000.0) if duration >= 1 else 0.0
            frames = int(st.get("frames", 0))
            large_ratio = int(st.get("large", 0)) / max(1, frames)
            small_ratio = int(st.get("small", 0)) / max(1, frames)
            retry_ratio = int(st.get("retry", 0)) / max(1, int(st.get("data_frames", 0)))

            session_secs = max(1, int(duration)+1)
            active_secs = len(st.get("seconds", {}))
            activity_ratio = min(1.0, active_secs/session_secs)
            tx_activity = min(1.0, len(st.get("tx_seconds", {}))/session_secs)
            presence_ratio = min(1.0, active_secs/max(1, int(capture_duration)+1))
            sec_rates = [b*8/1_000_000.0 for b in st.get("seconds", {}).values()]
            tx_sec_rates = [b*8/1_000_000.0 for b in st.get("tx_seconds", {}).values()]
            p95_rate = _percentile(sec_rates, 0.95)
            p95_tx_rate = _percentile(tx_sec_rates, 0.95)
            burst_cv = _cv(sec_rates)
            tx_rate_cv = _cv(tx_sec_rates)
            times = sorted(st.get("times", []))
            gaps = [b-a for a,b in zip(times, times[1:]) if 0 < b-a <= 30]
            gap_mean = _mean(gaps)
            gap_cv = _cv(gaps) if len(gaps) >= 10 else 99.0

            identity = 0
            reasons = []
            if any(w in vlow for w in camera_vendor_strong):
                identity = 20
                reasons.append("camera-oriented vendor/OUI" if is_en else "vendor camera")
            elif any(w in vlow for w in camera_vendor_mixed):
                identity = 10
                reasons.append("vendor with camera product line" if is_en else "vendor con linea telecamere")
            elif any(w in vlow for w in iot_vendor_words):
                identity = 8
                reasons.append("IoT-oriented vendor/OUI" if is_en else "vendor IoT")
            elif any(w in vlow for w in consumer_vendor_words):
                identity = -8
                reasons.append("generic client-device vendor" if is_en else "vendor client generico")

            direction = 0
            if duration >= 20 and tx >= 250000:
                if tx_ratio >= 0.80 and tx_bitrate >= 0.15:
                    direction = 23
                    reasons.append("video-like LAN uplink dominance" if is_en else "upload LAN compatibile con video")
                elif tx_ratio >= 0.65 and tx_bitrate >= 0.08:
                    direction = 17
                    reasons.append("LAN uplink-dominant traffic" if is_en else "upload LAN prevalente")
                elif tx_ratio >= 0.55:
                    direction = 9
                    reasons.append("TX>RX")

            continuity = 0
            if duration >= 60 and activity_ratio >= 0.70 and frames >= 180:
                continuity = 18
                reasons.append("continuous LAN traffic flow" if is_en else "flusso LAN continuo")
            elif duration >= 30 and activity_ratio >= 0.50 and frames >= 100:
                continuity = 13
                reasons.append("sustained LAN traffic" if is_en else "traffico LAN sostenuto")
            elif duration >= 12 and activity_ratio >= 0.35 and frames >= 40:
                continuity = 7
                reasons.append("persistent LAN session" if is_en else "sessione LAN persistente")
            if duration >= 30 and len(tx_sec_rates) >= 12 and tx_activity >= 0.45:
                if tx_rate_cv < 0.75:
                    continuity = min(18, continuity+4)
                    reasons.append("steady LAN uplink throughput" if is_en else "throughput upload LAN regolare")
                elif tx_rate_cv < 1.20:
                    continuity = min(18, continuity+2)

            shape = 0
            if large_ratio >= 0.55 and frames >= 60:
                shape += 7
                reasons.append("high proportion of large frames" if is_en else "molti frame grandi")
            elif large_ratio >= 0.35 and frames >= 50:
                shape += 4
            if bitrate >= 0.40 or p95_rate >= 1.0:
                shape += 6
                reasons.append(f"{bitrate:.2f} Mbps")
            elif bitrate >= 0.12:
                shape += 3
            if tx_activity >= 0.45 and p95_tx_rate >= 0.20:
                shape += 2
            shape = min(15, shape)

            temporal = 0
            if len(gaps) >= 20 and gap_mean > 0:
                if gap_cv < 0.55:
                    temporal = 6
                    reasons.append("regular timing pattern" if is_en else "temporizzazione regolare")
                elif gap_cv < 0.90:
                    temporal = 3

            # Bonus perché il MAC è stato visto come endpoint DS/LAN e non come station radio.
            lan_bonus = 0
            lan_score = 0
            try:
                lan_score = int(lan_det.get("score", 0) or 0)
            except Exception:
                lan_score = 0
            if frames >= 2:
                lan_bonus = 5
                reasons.append("observed as LAN/DS endpoint" if is_en else "osservato come endpoint LAN/DS")
            if lan_score >= 55:
                lan_bonus = 8

            penalty = 0
            if rx > tx*3 and bitrate >= 0.5:
                penalty += 15
                reasons.append("download-dominant traffic" if is_en else "download dominante")
            if burst_cv > 2.2 and activity_ratio < 0.30 and duration >= 20:
                penalty += 10
            if duration < 8 and frames > 0:
                penalty += 8
            if small_ratio > 0.80 and bitrate < 0.08 and frames >= 8:
                penalty += 8
            if retry_ratio >= 0.45 and int(st.get("data_frames",0)) >= 40:
                penalty += 6

            raw = identity + direction + continuity + shape + temporal + lan_bonus - penalty

            coverage = 0
            if duration >= 15: coverage += 1
            if duration >= 45: coverage += 1
            if frames >= 50: coverage += 1
            if frames >= 150: coverage += 1
            if len(gaps) >= 20: coverage += 1
            confidence = min(1.0, 0.42 + coverage*0.11)

            uncertainty = 10 if coverage <= 1 else (6 if coverage == 2 else (3 if coverage == 3 else 0))
            score = int(round(max(0, min(100, raw-uncertainty))))

            # FILTRO LAN V3:
            # - comportamento video resta il criterio principale;
            # - un MAC già realmente presente nella tabella LAN + vendor fortemente
            #   camera-oriented può essere recuperato anche se quasi inattivo;
            # - la sola discovery IP generica NON basta.
            behavior_score = direction + continuity + shape + temporal

            try:
                _lan_known = mac in (getattr(self, "lan_candidate_details", {}) or {})
                _lan_source = str(lan_det.get("source", "") or "").upper()
                _lan_passive_evidence = bool(
                    _lan_known and _lan_source not in ("ACTIVE-LAN", "")
                )
                if not _lan_passive_evidence and _lan_known:
                    _lan_passive_evidence = int(lan_det.get("ds_hits", 0) or 0) > 0
            except Exception:
                _lan_known = False
                _lan_passive_evidence = False

            # Firma specifica CAMERA LAN / CAMERA -> NVR osservabile sul DS.
            # Per una camera LAN che invia video verso un client/NVR attraversando
            # l'AP ci aspettiamo TX lato endpoint LAN persistente, attività distribuita
            # e frame/bitrate coerenti con un flusso video.
            lan_stream_strong = bool(
                duration >= 30 and frames >= 100
                and tx_ratio >= 0.72 and tx_bitrate >= 0.08
                and activity_ratio >= 0.40 and tx_activity >= 0.35
                and (large_ratio >= 0.25 or p95_tx_rate >= 0.30)
                and retry_ratio < 0.45
            )
            lan_stream_very_strong = bool(
                duration >= 45 and frames >= 180
                and tx_ratio >= 0.80 and tx_bitrate >= 0.15
                and activity_ratio >= 0.55 and tx_activity >= 0.45
                and (large_ratio >= 0.35 or p95_tx_rate >= 0.45)
            )
            if lan_stream_very_strong:
                score = min(100, score + 8)
                reasons.append(
                    "strong LAN camera/NVR video-stream signature"
                    if is_en else "forte firma stream video camera LAN/NVR"
                )
            elif lan_stream_strong:
                score = min(100, score + 4)
                reasons.append(
                    "LAN camera/NVR video-stream signature"
                    if is_en else "firma stream video camera LAN/NVR"
                )

            # MAC locale/randomizzato lato LAN: stesso principio anti-falso-positivo.
            try:
                _lan_local = bool(int(mac.split(":",1)[0],16) & 0x02)
            except Exception:
                _lan_local = False
            if _lan_local and identity < 20:
                continue

            if frames < 2:
                continue

            strong_behavior = (
                direction >= 9
                or continuity >= 7
                or shape >= 7
                or temporal >= 3
            )

            # Recupero camera LAN a basso traffico:
            # vendor camera forte + presenza LAN già confermata + almeno 2 frame DS.
            low_traffic_camera_vendor = (
                identity >= 20
                and _lan_known
                and frames >= 2
                and not related_radio_bssids
            )

            if not strong_behavior and not low_traffic_camera_vendor:
                continue

            if related_radio_bssids:
                # Su dual-band/mesh un client Wi-Fi dell'altra radio è indistinguibile
                # da un endpoint DS cablato guardando il solo Address3. Non promuoverlo
                # a camera LAN con segnali deboli/idle.
                if identity < 20:
                    if not (
                        frames >= 220 and duration >= 45 and tx_ratio >= 0.82
                        and activity_ratio >= 0.55 and large_ratio >= 0.35
                        and p95_tx_rate >= 0.35
                    ):
                        continue
                else:
                    if not strong_behavior or behavior_score < 16:
                        continue

            generic_video_signals = 0
            if tx_ratio >= 0.85 and direction >= 23:
                generic_video_signals += 1
            if duration >= 60 and continuity >= 13 and activity_ratio >= 0.60:
                generic_video_signals += 1
            if frames >= 220 and large_ratio >= 0.45 and shape >= 10:
                generic_video_signals += 1
            if tx_activity >= 0.55 and p95_tx_rate >= 0.45 and tx_rate_cv < 1.05:
                generic_video_signals += 1
            if temporal >= 3 and len(gaps) >= 25:
                generic_video_signals += 1

            if identity >= 20:
                # Vendor CCTV + endpoint DS reale: a basso traffico puo' entrare,
                # ma senza streaming resta DA OSSERVARE e non viene promosso.
                if not _lan_known and frames < 8:
                    continue
                if not strong_behavior and low_traffic_camera_vendor:
                    score = max(score, 44)
                    reasons.append(
                        "camera vendor + confirmed low-traffic LAN presence"
                        if is_en else "vendor camera + presenza LAN a basso traffico confermata"
                    )
                elif not lan_stream_strong and behavior_score < 10:
                    if duration < 20 or frames < 20:
                        continue
                    score = max(36, min(score, 41))
                    reasons.append(
                        "camera vendor on LAN but video stream not confirmed"
                        if is_en else "vendor camera LAN ma stream video non confermato"
                    )

            elif identity == 10:
                mixed_lan_mid = bool(
                    lan_stream_strong
                    and frames >= 100 and duration >= 35
                    and tx_ratio >= 0.68 and activity_ratio >= 0.40
                    and generic_video_signals >= 1
                )
                if not mixed_lan_mid:
                    continue
                if generic_video_signals < 2:
                    score = max(36, min(score, 41))

            else:
                # Host LAN generico: con 3+ segnali e' POSSIBILE; con 2 segnali
                # molto coerenti puo' comparire solo come DA OSSERVARE.
                generic_lan_mid = bool(
                    generic_video_signals >= 2
                    and lan_stream_strong
                    and frames >= 120 and duration >= 35
                    and tx_ratio >= 0.75 and bitrate >= 0.10
                    and small_ratio <= 0.65
                )
                if not generic_lan_mid:
                    continue
                if generic_video_signals == 2:
                    score = max(36, min(score, 41))
                reasons.append(
                    f"generic-vendor LAN video fingerprint {generic_video_signals}/5"
                    if is_en else f"impronta video LAN vendor generico {generic_video_signals}/5"
                )

            # Via di mezzo: DA OSSERVARE solo da 36/100 e soltanto dopo i filtri.
            if score < 36:
                continue
            if score >= 80:
                level = "HIGHLY LIKELY" if is_en else "MOLTO PROBABILE"
            elif score >= 62:
                level = "LIKELY" if is_en else "PROBABILE"
            elif score >= 42:
                level = "POSSIBLE" if is_en else "POSSIBILE"
            else:
                level = "LOW CONFIDENCE" if is_en else "DA OSSERVARE"

            txrx = f"{tx/1048576:.1f}/{rx/1048576:.1f} MB"
            dur = f"{duration:.0f} s"
            conf = int(round(confidence*100))
            unique = []
            for r in reasons:
                if r and r not in unique:
                    unique.append(r)
            indicators = ("; ".join(unique[:8]) or (
                "LAN/DS traffic compatible with camera behavior"
                if is_en else
                "traffico LAN/DS compatibile con comportamento telecamera"
            )) + f"; conf {conf}%"

            detail = {
                "mac": mac, "vendor": vendor, "score": score, "level": level,
                "confidence": conf, "class": "LAN", "provenance": "LAN",
                "frames": frames, "tx_frames": int(st.get("tx_frames",0)),
                "rx_frames": int(st.get("rx_frames",0)),
                "tx_bytes": tx, "rx_bytes": rx, "txrx": txrx,
                "duration": duration, "bitrate": bitrate, "tx_bitrate": tx_bitrate,
                "tx_ratio": tx_ratio, "activity_ratio": activity_ratio,
                "tx_activity": tx_activity, "presence": presence_ratio,
                "presence_ratio": presence_ratio, "continuity": activity_ratio,
                "continuity_score": continuity,
                "regularity": (0.0 if tx_rate_cv >= 90 else max(0.0,1.0-min(1.0,tx_rate_cv))),
                "avg_len": _mean(st.get("lengths",[])),
                "avg_frame_size": _mean(st.get("lengths",[])),
                "large_ratio": large_ratio, "small_ratio": small_ratio,
                "retry_ratio": retry_ratio, "gap_mean": gap_mean,
                "mean_iat": gap_mean, "inter_arrival": gap_mean,
                "gap_cv": gap_cv, "p95_rate": p95_rate,
                "p95_tx_rate": p95_tx_rate, "burst_cv": burst_cv,
                "tx_rate_cv": tx_rate_cv, "mean_signal": 0.0, "avg_signal": 0.0,
                "reasons": unique,
                "traffic_profile": (
                    "LAN CAMERA/NVR STREAMING" if lan_stream_very_strong else
                    "LAN CAMERA/NVR COMPATIBLE" if lan_stream_strong else
                    "LAN CAMERA LOW-TRAFFIC" if low_traffic_camera_vendor else
                    "LAN CAMERA-LIKE TRAFFIC"
                ),
                "brand_assessment": vendor if identity >= 20 else (
                    "NOT DETERMINABLE FROM TRAFFIC ALONE"
                    if is_en else "NON DETERMINABILE DAL SOLO TRAFFICO"
                ),
                "score_parts": {
                    "identita": identity, "protocollo": 0, "direzione": direction,
                    "continuita": continuity, "forma": shape, "temporale": temporal,
                    "radio": 0, "presenza": lan_bonus,
                    "penalita": penalty, "incertezza": uncertainty
                }
            }

            old_det = (getattr(self, "camera_candidate_details", {}) or {}).get(mac)
            try:
                old_score = int(old_det.get("score", -1)) if old_det else -1
            except Exception:
                old_score = -1
            if score >= old_score:
                self.camera_candidate_details[mac] = detail

            out.append((mac, vendor, f"{score}/100", level, txrx, "LAN", dur, indicators))

        return sorted(out, key=lambda r: (-int(r[2].split("/")[0]), r[0]))





    def _cascade_correlate_router_to_bssid(
        self, cap, visible_lan_macs=None, visible_client_macs=None, excluded_bssids=None
    ):
        """Correlazione separata WAN/LAN <-> BSSID.

        IMPORTANTE: la prima cattura è normalmente bloccata sul BSSID Netgear,
        quindi non può contenere beacon di un TP-Link su un altro canale.
        Per questo i BSSID candidati vengono presi PRIMA dalla tabella
        ROUTER RILEVATI (scansione multicanale già eseguita) e solo in aggiunta
        dai beacon eventualmente presenti nel PCAP.

        Il collegamento candidato può provenire da:
        1) un MAC realmente visibile nella tabella LAN (passivo DS o discovery attiva);
        2) una station Wi-Fi della scansione CLIENT, MA soltanto se ha firma
           router/repeater e forte somiglianza strutturale con un BSSID già rilevato.

        Gli endpoint DS della cattura vengono usati solo come evidenza aggiuntiva
        e non possono creare da soli l'avviso.
        """
        if not cap or not Path(cap).exists():
            return None
        is_en = getattr(self, "language", "it") == "en"

        # 1) BSSID già trovati dalla scansione ROUTER RILEVATI.
        aps = {}
        try:
            for iid in self.ap_tree.get_children(""):
                vals = self.ap_tree.item(iid, "values") or ()
                if len(vals) < 2:
                    continue
                b = str(vals[0] or "").strip().lower()
                if not MAC_FULL.match(b):
                    continue
                ch = str(vals[1] or "").strip()
                # colonne correnti:
                # BSSID, CANALE, POTENZA, ESSID, BANDA, CLIENTI, PACCHETTI, CRIPTAZIONE
                ssid = str(vals[3] or "").strip() if len(vals) > 3 else ""
                aps[b] = {"ssid": ssid, "channel": ch, "hits": 5, "source": "ROUTER RILEVATI"}
        except Exception:
            pass

        # 2) Integra eventuali beacon/probe response presenti nel PCAP.
        try:
            p = run([
                "tshark","-r",str(cap),
                "-Y","wlan.fc.type == 0 && (wlan.fc.subtype == 8 || wlan.fc.subtype == 5)",
                "-T","fields","-E","separator=|","-E","occurrence=f",
                "-e","wlan.bssid","-e","wlan.ssid","-e","wlan_radio.channel"
            ], timeout=20)
            for line in (p.stdout or "").splitlines():
                c=line.split("|")
                if len(c)<3: continue
                b=str(c[0] or "").strip().lower()
                if not MAC_FULL.match(b): continue
                ssid=str(c[1] or "").strip()
                ch=str(c[2] or "").strip().split(",",1)[0]
                rec=aps.setdefault(b,{"ssid":ssid,"channel":ch,"hits":0,"source":"PCAP"})
                rec["hits"]+=1
                if ssid: rec["ssid"]=ssid
                if ch.isdigit(): rec["channel"]=ch
        except Exception:
            pass
        if not aps:
            return None

        # 3) La correlazione router-cascata può partire SOLO da un MAC che è
        # realmente comparso nella maschera/tabella LAN. Gli endpoint DS presenti
        # nel PCAP servono soltanto ad arricchire il punteggio: da soli NON possono
        # più generare l'avviso. Questo evita il popup quando la tabella LAN è vuota.
        lan_visible_macs = set()

        # Se il chiamante passa i MAC del segmento appena analizzato, usa SOLO
        # quelli. È fondamentale nelle cascate multilivello: i LAN della scansione
        # precedente restano nella GUI, ma non devono pilotare la correlazione del
        # segmento corrente.
        if visible_lan_macs is not None:
            try:
                for _m in (visible_lan_macs or set()):
                    _m = str(_m or "").strip().lower()
                    if MAC_FULL.match(_m) and not self.is_multicast_or_broadcast(_m):
                        lan_visible_macs.add(_m)
            except Exception:
                pass
        else:
            try:
                tree = getattr(self, "lan_vendor_tree", None)
                if tree is not None:
                    for iid in tree.get_children(""):
                        vals = tree.item(iid, "values") or ()
                        # Layout tabella LAN corrente:
                        # VENDOR, RUOLO, NOTE, SCORE/EVIDENZA, MAC
                        if len(vals) < 5:
                            continue
                        m = str(vals[4] or "").strip().lower()
                        if MAC_FULL.match(m) and not self.is_multicast_or_broadcast(m):
                            lan_visible_macs.add(m)
            except Exception:
                pass

        # I BSSID/AP noti sono infrastruttura radio, non MAC WAN/LAN.
        lan_visible_macs.difference_update(self._known_ap_bssids())
        try:
            _main_bssid = str(getattr(self,"bssid",tk.StringVar()).get() or "").strip().lower()
            lan_visible_macs.discard(_main_bssid)
        except Exception:
            pass

        client_visible_macs = set()
        try:
            for _m in (visible_client_macs or set()):
                _m = str(_m or "").strip().lower()
                if MAC_FULL.match(_m) and not self.is_multicast_or_broadcast(_m):
                    client_visible_macs.add(_m)
        except Exception:
            pass
        client_visible_macs.difference_update(self._known_ap_bssids())

        # Nessuna prova LAN e nessuna station router/repeater = nessun avviso.
        if not lan_visible_macs and not client_visible_macs:
            return None

        # Le sorgenti restano distinte: LAN/DS ha priorità; CLIENT Wi-Fi viene
        # accettato solo con criteri strutturali/vendor più severi.
        endpoints = {}
        for m in lan_visible_macs:
            endpoints[m] = {"hits": 0, "fromds": 0, "tods": 0, "source": "LAN"}
        for m in client_visible_macs:
            endpoints.setdefault(
                m, {"hits": 0, "fromds": 0, "tods": 0, "source": "CLIENT-WIFI"}
            )

        # Le statistiche DS del PCAP sono opzionali e vengono attribuite soltanto
        # ai MAC già presenti nella tabella LAN; non creano nuovi candidati.
        try:
            p = run([
                "tshark","-r",str(cap),"-Y","wlan.fc.type == 2",
                "-T","fields","-E","separator=|","-E","occurrence=f",
                "-e","wlan.fc.tods","-e","wlan.fc.fromds",
                "-e","wlan.sa","-e","wlan.da","-e","wlan.bssid"
            ], timeout=20)
            for line in (p.stdout or "").splitlines():
                c=line.split("|")
                if len(c)<5: continue
                td=str(c[0]).strip() in ("1","True","true")
                fd=str(c[1]).strip() in ("1","True","true")
                sa=str(c[2] or "").strip().lower()
                da=str(c[3] or "").strip().lower()
                fb=str(c[4] or "").strip().lower()
                ep=""
                if fd and not td: ep=sa
                elif td and not fd: ep=da
                if ep not in lan_visible_macs:
                    continue
                if ep == fb or self.is_multicast_or_broadcast(ep):
                    continue
                r=endpoints[ep]
                r["hits"]+=1
                if fd: r["fromds"]+=1
                if td: r["tods"]+=1
        except Exception:
            # La somiglianza MAC può essere valutata comunque sui MAC LAN visibili.
            pass

        # MAC già provati come vere station radio sul BSSID principale:
        # non considerarli WAN Ethernet di un router cascata.
        radio=set(getattr(self,"wifi_radio_macs_session",set()) or set())

        router_words=("tp-link","tplink","netgear","d-link","dlink","asus","zyxel",
                      "mikrotik","ubiquiti","mercusys","tenda","linksys",
                      "huawei","zte","xiaomi","vodafone","technicolor",
                      "vantiva","sagemcom","sercomm","arcadyan")

        excluded_bssids = {
            str(_b or "").strip().lower()
            for _b in (excluded_bssids or set())
            if MAC_FULL.match(str(_b or "").strip().lower())
        }

        best=None
        for wan,st in endpoints.items():
            # Il requisito per entrare qui e' gia' la presenza nella tabella LAN.
            # Se il MAC e' stato visto anche via radio non lo eliminiamo: una
            # topologia bridge/mesh puo' renderlo ambiguo. La prova radio abbassa
            # soltanto la confidenza, mentre la somiglianza MAC resta obbligatoria.
            _wan_radio_ambiguous = wan in radio
            try:
                wv=str(self.resolve_mac_with_manuf(wan) or "").strip()
            except Exception:
                wv=""
            # Fallback OUI per famiglie router comuni osservabili anche quando
            # il database manuf locale non è installato/aggiornato.
            oui=wan[:8]
            known_router_ouis={
                "70:4f:57":"TP-Link","30:b5:c2":"TP-Link","3c:46:d8":"TP-Link",
                "5c:a6:e6":"TP-Link","7c:8b:ca":"TP-Link","84:16:f9":"TP-Link",
                "9c:a2:f4":"TP-Link","a8:57:4e":"TP-Link","ac:84:c6":"TP-Link",
                "b8:d5:26":"TP-Link","c4:6e:1f":"TP-Link","d4:6e:0e":"TP-Link",
                "d8:eb:46":"TP-Link","e0:05:c5":"TP-Link",
                "08:16:05":"Vodafone"
            }
            if not wv and oui in known_router_ouis:
                wv=known_router_ouis[oui]

            for b,ap in aps.items():
                if b in excluded_bssids:
                    continue
                if b == str(getattr(self,"bssid",tk.StringVar()).get() if hasattr(self,"bssid") else "").lower():
                    # non proporre come scansione successiva lo stesso AP corrente
                    continue
                try:
                    bv=str(self.resolve_mac_with_manuf(b) or "").strip()
                except Exception:
                    bv=""
                boui=b[:8]
                if not bv and boui in known_router_ouis:
                    bv=known_router_ouis[boui]

                try:
                    dist=abs(int(b.replace(":",""),16)-int(wan.replace(":",""),16))
                except Exception:
                    dist=10**12
                same_oui=(oui==boui)
                same_vendor=bool(wv and bv and (
                    wv.lower() in bv.lower() or bv.lower() in wv.lower()
                ))
                wan_router=any(x in wv.lower() for x in router_words) if wv else False
                b_router=any(x in bv.lower() for x in router_words) if bv else False

                # Requisito strutturale: l'avviso cascata deve nascere da un MAC
                # LAN realmente SIMILE a uno dei BSSID gia' rilevati, non dal solo
                # fatto che i due vendor siano uguali. Manteniamo i due criteri
                # usati nel progetto: 4 byte centrali uguali oppure distanza MAC
                # numerica <= 256.
                try:
                    middle4_match = wan.split(":")[1:5] == b.split(":")[1:5]
                except Exception:
                    middle4_match = False
                mac_similar = bool(middle4_match or dist <= 256)
                if not mac_similar:
                    continue

                source_kind = str(st.get("source", "LAN") or "LAN")
                source_is_client = source_kind == "CLIENT-WIFI"

                # Una station Wi-Fi può pilotare la cascata soltanto se sembra
                # davvero un router/repeater: niente client generici.
                if source_is_client:
                    router_identity_ok = bool(
                        (wan_router and b_router and (same_vendor or same_oui))
                        or (same_oui and (wan_router or b_router))
                    )
                    if not router_identity_ok:
                        continue

                score=0; reasons=[]
                if source_is_client:
                    score += 8
                    reasons.append(
                        "router/repeater seen as Wi-Fi station"
                        if is_en else
                        "router/repeater visto come station Wi-Fi"
                    )
                else:
                    score += 8
                    reasons.append(
                        "device visible in LAN evidence"
                        if is_en else
                        "dispositivo visibile nelle prove LAN"
                    )

                if middle4_match:
                    score += 18
                    reasons.append("matching 4 middle MAC bytes" if is_en else "4 byte centrali MAC uguali")
                # La prova più importante: endpoint DS e AP appartengono allo
                # stesso produttore di router. Non richiediamo MAC adiacenti:
                # WAN e radio possono provenire da blocchi MAC differenti.
                if same_oui:
                    score+=42; reasons.append("same OUI" if is_en else "stesso OUI")
                if same_vendor and wan_router and b_router:
                    score+=38; reasons.append("same router vendor" if is_en else "stesso vendor router")
                elif wan_router and b_router:
                    score+=24; reasons.append("router vendors compatible" if is_en else "vendor compatibili router")
                if dist<=4:
                    score+=28; reasons.append("MAC distance <= 4")
                elif dist<=32:
                    score+=20; reasons.append("MAC distance <= 32")
                elif dist<=256:
                    score+=10; reasons.append("MAC distance <= 256")
                if st["fromds"]>0 and st["tods"]>0:
                    score+=12; reasons.append("bidirectional DS endpoint" if is_en else "endpoint DS bidirezionale")
                elif st["hits"]>=2:
                    score+=5
                if ap.get("source")=="ROUTER RILEVATI":
                    score+=8; reasons.append("AP seen in router scan" if is_en else "AP visto nella scansione router")
                if _wan_radio_ambiguous:
                    score -= 18
                    reasons.append(
                        "LAN MAC also seen as Wi-Fi station: ambiguous bridge/mesh evidence"
                        if is_en else
                        "MAC LAN visto anche come station Wi-Fi: evidenza bridge/mesh ambigua"
                    )

                # Preferenza 2.4 GHz per la seconda scansione dedicata.
                # Non esclude 5 GHz: lo penalizza soltanto quando esiste una
                # correlazione 2.4 GHz plausibile dello stesso router.
                try:
                    _ch_i = int(str(ap.get("channel","")).strip())
                except Exception:
                    _ch_i = 0
                if 1 <= _ch_i <= 14:
                    score += 14
                    reasons.append("2.4 GHz preferred" if is_en else "preferenza 2.4 GHz")
                elif _ch_i > 14:
                    score -= 6

                score=max(0,min(100,score))

                cand={"wan_mac":wan,"wan_vendor":wv,"bssid":b,
                      "ssid":ap.get("ssid",""),"channel":ap.get("channel",""),
                      "score":score,"vendor":bv,"reasons":reasons,
                      "link_source":source_kind,
                      "ds_hits":st["hits"],"fromds":st["fromds"],"tods":st["tods"]}
                if best is None:
                    best=cand
                else:
                    try:
                        _cand24 = 1 <= int(str(cand.get("channel",""))) <= 14
                    except Exception:
                        _cand24 = False
                    try:
                        _best24 = 1 <= int(str(best.get("channel",""))) <= 14
                    except Exception:
                        _best24 = False

                    # Il punteggio resta la prova principale. Se due candidati
                    # sono vicini (entro 12 punti), scegli il 2.4 GHz.
                    if cand["score"] > best["score"]:
                        best=cand
                    elif _cand24 and not _best24 and cand["score"] >= best["score"] - 12:
                        best=cand

        # MODALITA' SENSIBILITA': la somiglianza strutturale MAC e la presenza
        # reale nella tabella LAN restano obbligatorie; lo score minimo viene pero'
        # abbassato per proporre la seconda scansione anche nei casi deboli.
        if not best or not str(best.get("channel","")).isdigit():
            return None
        _min_score = 55 if str(best.get("link_source","")) == "CLIENT-WIFI" else 35
        return best if int(best.get("score",0)) >= _min_score else None


    def _cascade_target_is_dual_band_sibling(self, target_bssid, stage_bssids=None):
        """True se il candidato CASCATA è in realtà la radio 2.4/5 GHz dello stesso router.

        Riusa il motore dual-band prima di mostrare il popup arancione, così una
        radio sorella non può essere riclassificata come router in cascata dopo
        che la proposta dual-band è stata già gestita o rifiutata.
        """
        target = str(target_bssid or "").strip().lower()
        if not MAC_FULL.match(target):
            return False

        stage = {
            str(b or "").strip().lower()
            for b in (stage_bssids or set())
            if MAC_FULL.match(str(b or "").strip().lower())
        }
        try:
            cur = str(self._dual_band_value(getattr(self, "bssid", "")) or "").strip().lower()
            if MAC_FULL.match(cur):
                stage.add(cur)
        except Exception:
            pass

        def _channel_for_bssid(bssid):
            try:
                for iid in self.ap_tree.get_children(""):
                    vals = tuple(self.ap_tree.item(iid, "values") or ())
                    if len(vals) > 1 and str(vals[0]).strip().lower() == bssid:
                        return str(vals[1]).strip()
            except Exception:
                pass
            try:
                for vals in (getattr(self, "_dual_band_ap_snapshot", {}) or {}).values():
                    vals = tuple(vals or ())
                    if len(vals) > 1 and str(vals[0]).strip().lower() == bssid:
                        return str(vals[1]).strip()
            except Exception:
                pass
            try:
                hist = self._network_graph_ensure_history()
                vals = tuple((hist.get("routers", {}) or {}).get(bssid, ()) or ())
                if len(vals) > 1:
                    return str(vals[1]).strip()
            except Exception:
                pass
            return ""

        for source_bssid in stage:
            ch = _channel_for_bssid(source_bssid)
            if not ch:
                continue
            try:
                sibling = self._find_same_bssid_other_band(source_bssid, ch, "")
            except Exception:
                sibling = None
            if sibling and str(sibling.get("bssid", "") or "").strip().lower() == target:
                try:
                    self.command_debug_write(
                        f"[CASCATA] SOPPRESSA: {target} riconosciuto come altra banda di {source_bssid}."
                    )
                except Exception:
                    pass
                return True
        return False


    def _cascade_offer_second_scan(self, cap, observed_rows=None, stage_bssids=None):
        """Propone la scansione del prossimo router/AP correlato.

        Funziona anche su più livelli:
            ROUTER PRINCIPALE -> AP/ROUTER 1 -> AP/ROUTER 2 -> ...

        Non ripropone mai un BSSID già scannerizzato nella stessa sessione.
        """
        if getattr(self, "_cascade_second_scan_running", False):
            return

        if not isinstance(getattr(self, "_cascade_scanned_bssids", None), set):
            self._cascade_scanned_bssids = set()
        if not isinstance(getattr(self, "_cascade_declined_bssids", None), set):
            self._cascade_declined_bssids = set()

        try:
            _cur = str(self._dual_band_value(getattr(self, "bssid", "")) or "").strip().lower()
            if MAC_FULL.match(_cur):
                self._cascade_scanned_bssids.add(_cur)
        except Exception:
            pass

        # Sicurezza contro catene patologiche/falsi match.
        if len(self._cascade_scanned_bssids) >= 8:
            try:
                self.logmsg("Cascata: limite di 8 BSSID analizzati nella sessione raggiunto.")
            except Exception:
                pass
            return

        current_segment_lan = None
        if observed_rows is not None:
            current_segment_lan = set()
            try:
                for _r in (observed_rows or []):
                    if len(_r) < 3 or str(_r[2]) != "LAN CANDIDATO":
                        continue
                    _m = str(_r[0] or "").strip().lower()
                    if MAC_FULL.match(_m) and not self.is_multicast_or_broadcast(_m):
                        current_segment_lan.add(_m)
            except Exception:
                pass

            # BUG FIX: il vecchio codice, quando riceveva observed_rows,
            # ignorava completamente active_lan_results. Con PCAP senza DATA/DS
            # questo produceva una tabella/correlazione vuota anche se arp-scan/nmap
            # avevano realmente trovato il router Vodafone sul segmento corrente.
            try:
                _cur_bssid = str(self._dual_band_value(getattr(self, "bssid", "")) or "").strip().lower()
                _info = getattr(self, "active_lan_scan_info", {}) or {}
                _method = str(_info.get("method", "") or "")
                _active_target = str(
                    _info.get("target_bssid") or _info.get("connected_bssid") or ""
                ).strip().lower()
                _stage_for_active = {
                    str(_b or "").strip().lower()
                    for _b in (stage_bssids or set())
                    if MAC_FULL.match(str(_b or "").strip().lower())
                }
                _active_valid = bool(
                    not _method.startswith("SUPPRESSED-")
                    and (
                        not _active_target
                        or _active_target == _cur_bssid
                        or _active_target in _stage_for_active
                    )
                )
                if _active_valid:
                    for _m in (getattr(self, "active_lan_results", {}) or {}):
                        _m = str(_m or "").strip().lower()
                        if MAC_FULL.match(_m) and not self.is_multicast_or_broadcast(_m):
                            current_segment_lan.add(_m)
            except Exception:
                pass

        # Un router/repeater può essere a cascata anche come uplink Wi-Fi.
        # In quel caso il suo MAC compare nella scansione CLIENT, non nel DS LAN.
        current_segment_clients = set()
        try:
            _cur_bssid = str(self._dual_band_value(getattr(self, "bssid", "")) or "").strip().lower()
            for _iid in self.client_tree.get_children(""):
                _vals = tuple(self.client_tree.item(_iid, "values") or ())
                if not _vals:
                    continue
                _m = str(_vals[0] or "").strip().lower()
                if not MAC_FULL.match(_m) or self.is_multicast_or_broadcast(_m):
                    continue
                _src = str(_vals[6] if len(_vals) > 6 else "")
                _src_bssid = self._scan_source_parent_bssid(_src, _cur_bssid)
                _stage_for_clients = {
                    str(_b or "").strip().lower()
                    for _b in (stage_bssids or set())
                    if MAC_FULL.match(str(_b or "").strip().lower())
                }
                if (
                    _src_bssid == _cur_bssid
                    or _src_bssid in _stage_for_clients
                ):
                    current_segment_clients.add(_m)
        except Exception:
            pass

        _stage_bssids = {
            str(_b or "").strip().lower()
            for _b in (stage_bssids or set())
            if MAC_FULL.match(str(_b or "").strip().lower())
        }
        _cascade_excluded = set(self._cascade_scanned_bssids) | _stage_bssids

        match = self._cascade_correlate_router_to_bssid(
            cap,
            visible_lan_macs=current_segment_lan,
            visible_client_macs=current_segment_clients,
            excluded_bssids=_cascade_excluded,
        )
        if not match:
            return

        _target = str(match.get("bssid", "") or "").strip().lower()
        if _target in self._cascade_scanned_bssids:
            try:
                self.command_debug_write(
                    f"[CASCATA] proposta soppressa: {_target} già scannerizzato."
                )
            except Exception:
                pass
            return
        if _target in self._cascade_declined_bssids:
            try:
                self.command_debug_write(
                    f"[CASCATA] proposta soppressa: {_target} già rifiutato con NO."
                )
            except Exception:
                pass
            return

        # Controllo di precedenza: una radio 2.4/5 GHz dello stesso router
        # non deve mai essere proposta come ROUTER IN CASCATA.
        if self._cascade_target_is_dual_band_sibling(_target, stage_bssids):
            try:
                self.logmsg(
                    ("Cascade suppressed: candidate is the other Wi-Fi band: "
                     if getattr(self, "language", "it") == "en"
                     else "Cascata soppressa: il candidato è l'altra banda Wi-Fi: ")
                    + _target
                )
            except Exception:
                pass
            return

        self._cascade_pending_match = match

        is_en = getattr(self,"language","it") == "en"
        msg = (
            ("POSSIBLE CASCADE ROUTER / BSSID CORRELATION\n\n"
             if is_en else "POSSIBILE CORRELAZIONE ROUTER CASCATA / BSSID\n\n")
            + (
                ("Linked MAC: " if is_en else "MAC collegato: ")
                + match["wan_mac"] + "\n"
            )
            + (
                ("Evidence source: " if is_en else "Origine evidenza: ")
                + (
                    "Wi-Fi client / router uplink"
                    if match.get("link_source") == "CLIENT-WIFI" and is_en
                    else "CLIENT Wi-Fi / uplink router"
                    if match.get("link_source") == "CLIENT-WIFI"
                    else "LAN / Distribution System"
                )
                + "\n"
            )
            + "BSSID: " + match["bssid"] + "\n"
            + "SSID: " + (match["ssid"] or "-") + "\n"
            + ("Channel: " if is_en else "Canale: ") + str(match["channel"]) + "\n"
            + ("Correlation: " if is_en else "Correlazione: ") + str(match["score"]) + "/100\n\n"
            + ("Start a 120-second passive scan on this BSSID?\n"
               "The results of the first scan will be preserved and integrated."
               if is_en else
               "Avviare una scansione passiva di 120 secondi su questo BSSID?\n"
               "I risultati della prima scansione saranno conservati e integrati.")
        )
        # Router in cascata: cornice ARANCIONE per distinguerlo dall'avviso dual-band.
        _cascade_yes = self._askyesno_colored_border(
            "Cascade router - PASSIVE CAPTURE"
            if is_en else
            "Router in cascata - CATTURA PASSIVA",
            msg,
            "#F57C00"
        )
        if _cascade_yes:
            try:
                self.command_debug_write(
                    f"[CASCATA] SI: nuova cattura passiva su {_target} "
                    f"ch {match.get('channel','')}"
                )
            except Exception:
                pass
            self._cascade_start_second_scan(match)
        else:
            # NO significa fine della procedura per questo router correlato.
            # Non viene riproposto durante la stessa sessione.
            self._cascade_declined_bssids.add(_target)
            self._cascade_pending_match = None
            try:
                self.logmsg(
                    ("Cascade router: NO selected; no further passive scan for "
                     if is_en else
                     "Router in cascata: scelto NO; nessuna ulteriore scansione passiva per ")
                    + _target
                )
                self.command_debug_write(
                    f"[CASCATA] NO: {_target}; procedura terminata."
                )
            except Exception:
                pass


    def _cascade_start_second_scan(self, match):
        """Seconda scansione dedicata al BSSID correlato.

        Motore separato: conserva i risultati della prima scansione, aggiorna
        esplicitamente il target visibile nella GUI e soltanto dopo avvia la
        cattura sul BSSID/canale proposti.
        """
        target_bssid = str(match.get("bssid", "") or "").strip().lower()
        target_ch = str(match.get("channel", "") or "").strip()

        if not MAC_FULL.match(target_bssid) or not target_ch.isdigit():
            messagebox.showwarning(
                "Cascade router" if getattr(self,"language","it")=="en" else "Router in cascata",
                "Invalid correlated BSSID/channel."
                if getattr(self,"language","it")=="en"
                else "BSSID/canale correlato non valido."
            )
            return

        if not isinstance(getattr(self, "_cascade_scanned_bssids", None), set):
            self._cascade_scanned_bssids = set()
        self._cascade_scanned_bssids.add(target_bssid)

        # Conserva la prima cattura e ne marca chiaramente la provenienza
        # prima di cambiare il BSSID visibile.
        try:
            _src_bssid = str(self._dual_band_value(getattr(self, "bssid", "")) or "").strip().lower()
            _src_ch = str(self._dual_band_value(getattr(self, "channel", "")) or "").strip()
            self._prepare_correlated_passive_preservation(
                _src_bssid, _src_ch, target_bssid, target_ch, "cascade"
            )
        except Exception:
            pass

        # Questa è una vera continuazione della prima cattura: il segmento
        # successivo verrà unito allo stesso PCAP definitivo.
        try:
            self._capture_chain_register_expected_second_scan(target_bssid, "cascade")
        except Exception:
            pass

        # Conserva PRIMA lo stato della prima scansione: tra poche righe il BSSID
        # visibile verrà sostituito con quello del router in cascata.
        try:
            _graph_parent_bssid = self._dual_band_value(getattr(self, "bssid", ""))
        except Exception:
            _graph_parent_bssid = ""
        try:
            self._network_graph_snapshot_current(_graph_parent_bssid, "cascade first scan")
            self._network_graph_register_cascade(
                _graph_parent_bssid, match.get("wan_mac", ""), target_bssid
            )
        except Exception:
            pass

        # Memorizza il target in variabili dedicate: non dipende più dal router
        # che era selezionato durante la prima cattura.
        # Nuovo router fisico in cascata = nuovo livello.
        # Prima di cercarne eventuali figli, verranno esaurite le sue bande.
        self._passive_router_stage_reset(target_bssid)

        self._cascade_second_scan_running = True
        self._cascade_second_scan_cameras = {}
        self._cascade_second_scan_target_bssid = target_bssid
        self._cascade_second_scan_target_channel = target_ch
        self._preserve_results_for_cascade_scan = True

        self._cascade_first_camera_rows = dict(getattr(self, "camera_candidate_rows", {}) or {})
        self._cascade_first_camera_details = dict(getattr(self, "camera_candidate_details", {}) or {})
        self._cascade_router_cam_placeholders = set()
        try:
            for _m, _d in self._cascade_first_camera_details.items():
                _d = _d or {}
                if _d.get("cascade_camera_candidate") or str(_d.get("class","")).upper() == "CASCADE ROUTER":
                    self._cascade_router_cam_placeholders.add(str(_m).lower())
        except Exception:
            pass
        # Rimane attivo per tutta la seconda sessione e viene consumato dal
        # merge GUI quando compare una vera camera sul BSSID correlato.
        self._cascade_router_cam_integration_active = True
        self._cascade_router_cam_finalize_merge = False
        self._cascade_first_lan_rows = dict(getattr(self, "lan_persistent_rows", {}) or {})
        self._cascade_first_lan_details = dict(getattr(self, "lan_persistent_details", {}) or {})

        # Aggiorna SUBITO ciò che l'utente vede vicino ad AVVIA CATTURA e nel
        # riquadro BLOCCO. In questo modo è evidente quale AP verrà osservato.
        self.bssid.set(target_bssid)
        self.channel.set(target_ch)
        self.client.set("")
        try:
            self.block_router_value.set(target_bssid)
            self.block_client_value.set("")
        except Exception:
            pass

        # Se il BSSID esiste ancora nella tabella ROUTER RILEVATI, selezionalo
        # anche graficamente senza richiamare on_ap_select (che potrebbe cambiare
        # nuovamente il target).
        try:
            for _iid in self.ap_tree.get_children(""):
                _vals = self.ap_tree.item(_iid, "values") or ()
                if _vals and str(_vals[0]).strip().lower() == target_bssid:
                    self.ap_tree.selection_set(_iid)
                    self.ap_tree.focus(_iid)
                    self.ap_tree.see(_iid)
                    break
        except Exception:
            pass

        try:
            self._update_capture_panel_titles()
            self._refresh_language_dynamic_texts()
        except Exception:
            pass

        try:
            # La seconda scansione automatica/correlata dura 120 secondi.
            self.capture_duration.set(120)
        except Exception:
            pass

        self.set_status(
            (f"SECOND PASSIVE SCAN: target {target_bssid} / channel {target_ch}"
             if getattr(self,"language","it")=="en"
             else f"SECONDA SCANSIONE PASSIVA: target {target_bssid} / canale {target_ch}")
        )
        self.logmsg(
            ("CASCADE SECOND SCAN -> " if getattr(self,"language","it")=="en"
             else "SECONDA SCANSIONE CASCATA -> ")
            + f"BSSID {target_bssid} | CH {target_ch}"
        )

        # Lascia a Tk il tempo di ridisegnare BSSID/canale prima di partire.
        # Al momento dell'avvio riafferma il target, così una callback tardiva
        # della prima scansione non può riportare il Netgear.
        def _launch_cascade_second_scan():
            self.bssid.set(target_bssid)
            self.channel.set(target_ch)
            self.client.set("")
            try:
                self.block_router_value.set(target_bssid)
                self.block_client_value.set("")
                self._update_capture_panel_titles()
            except Exception:
                pass

            iface = self.validate_monitor_iface()
            if not iface:
                self._cascade_second_scan_running = False
                return

            # Imposta esplicitamente il canale del BSSID TP-Link prima che
            # start_capture costruisca il worker.
            try:
                r = run(["iw","dev",iface,"set","channel",target_ch], timeout=5)
                if r.returncode != 0:
                    raise RuntimeError((r.stderr or r.stdout or "").strip())
            except Exception as e:
                self._cascade_second_scan_running = False
                messagebox.showerror(
                    "Cascade router" if getattr(self,"language","it")=="en" else "Router in cascata",
                    (f"Unable to set channel {target_ch} for {target_bssid}:\n{e}"
                     if getattr(self,"language","it")=="en"
                     else f"Impossibile impostare il canale {target_ch} per {target_bssid}:\n{e}")
                )
                return

            # Ultimo controllo: il target mostrato e quello passato alla cattura
            # devono essere esattamente quelli correlati.
            self.bssid.set(target_bssid)
            self.channel.set(target_ch)
            self.start_capture()

        self.root.after(180, _launch_cascade_second_scan)


    def _analyze_cascade_router_camera_candidates(self, cap, bssid):
        """Non promuove piu' un router/gateway a telecamera.

        La presenza di un router in cascata viene gestita esclusivamente dalla
        correlazione LAN-MAC <-> BSSID e dalla seconda scansione dedicata. Un
        router e' infrastruttura e non deve comparire in POSSIBILI TELECAMERE.
        """
        return []


    def _analyze_dvr_nvr_candidates_separate(self, existing_lan_rows, observed_rows=None, cap=None, bssid=""):
        """Algoritmo DVR/NVR separato. Non modifica lo score telecamere."""
        is_en = getattr(self, "language", "it") == "en"
        result = []

        # Un router/AP non puo' essere promosso a NVR. Manteniamo una blacklist
        # infrastrutturale separata dal motore LAN, cosi' il router puo' ancora
        # comparire come apparato LAN ma MAI nel riquadro telecamere/NVR.
        _nvr_infrastructure = set(self._known_ap_bssids())
        _bssid_arg = str(bssid or "").replace("(*)", "").strip().lower()
        if MAC_FULL.match(_bssid_arg):
            _nvr_infrastructure.add(_bssid_arg)
        try:
            for _rel in (getattr(self, "_network_graph_relations", []) or []):
                _w = str(_rel.get("wan", "") or "").strip().lower()
                if MAC_FULL.match(_w):
                    _nvr_infrastructure.add(_w)
        except Exception:
            pass
        _router_vendor_words = (
            "zte", "tp-link", "tplink", "netgear", "d-link", "dlink", "asus",
            "zyxel", "mikrotik", "ubiquiti", "mercusys", "tenda", "linksys",
            "huawei", "vodafone", "technicolor", "vantiva", "thomson",
            "sagemcom", "sercomm", "arcadyan"
        )

        def _looks_like_router_interface(_mac, _vendor=""):
            _mac = str(_mac or "").strip().lower()
            if _mac in _nvr_infrastructure:
                return True
            try:
                if self._is_camera_infrastructure_mac(_mac, _vendor):
                    return True
            except Exception:
                pass
            _vl = str(_vendor or "").lower()
            if not any(_w in _vl for _w in _router_vendor_words):
                return False
            try:
                _mi = int(_mac.replace(":", ""), 16)
            except Exception:
                return False
            for _ap in _nvr_infrastructure:
                try:
                    if _mac[:8] == _ap[:8] and abs(_mi - int(_ap.replace(":", ""), 16)) <= 32:
                        return True
                except Exception:
                    pass
            return False

        # Lavora sui dettagli LAN già prodotti dall'analisi passiva, ma
        # integra anche observed_rows: un DVR/NVR molto silenzioso può apparire
        # nel PCAP con una sola evidenza DS e non avere ancora metriche camera.
        details_map = dict(getattr(self, "lan_candidate_details", {}) or {})
        for _row in observed_rows or []:
            if len(_row) < 5:
                continue
            _mac, _vendor, _cls, _evidence, _notes = _row[:5]
            _mac = str(_mac or "").lower()
            if not MAC_FULL.match(_mac):
                continue
            if _mac in _nvr_infrastructure:
                continue
            if str(_cls) != "LAN CANDIDATO":
                continue
            _d = dict(details_map.get(_mac, {}) or {})
            _d.setdefault("mac", _mac)
            _d.setdefault("vendor", str(_vendor or ""))
            _d.setdefault("evidence", str(_evidence or ""))
            _d.setdefault("notes", str(_notes or ""))
            details_map[_mac] = _d

        # SECONDO CANALE DI ANALISI, COMPLETAMENTE SEPARATO:
        # legge direttamente il PCAP e raccoglie endpoint DS anche quando il
        # normale filtro LAN non li ha ancora promossi. Questo è fondamentale
        # per DVR/NVR estremamente silenziosi (anche 1 solo frame in 2 minuti).
        direct_ds = {}
        if cap and Path(cap).exists():
            try:
                _cmd = [
                    "tshark", "-r", str(cap),
                    "-Y", "wlan.fc.type == 2",
                    "-T", "fields", "-E", "separator=|", "-E", "occurrence=f",
                    "-e", "frame.time_epoch",
                    "-e", "wlan.fc.tods", "-e", "wlan.fc.fromds",
                    "-e", "wlan.sa", "-e", "wlan.da", "-e", "wlan.bssid",
                    "-e", "frame.len"
                ]
                _p = run(_cmd, timeout=20)
                for _line in (_p.stdout or "").splitlines():
                    _c = _line.split("|")
                    if len(_c) < 7:
                        continue
                    try:
                        _ts = float(_c[0] or 0)
                    except Exception:
                        _ts = 0.0
                    _tods = str(_c[1]).strip() in ("1", "True", "true")
                    _fromds = str(_c[2]).strip() in ("1", "True", "true")
                    _sa = str(_c[3] or "").strip().lower()
                    _da = str(_c[4] or "").strip().lower()
                    _fbssid = str(_c[5] or "").strip().lower()
                    try:
                        _flen = int(_c[6] or 0)
                    except Exception:
                        _flen = 0

                    # Solo traffico relativo al BSSID selezionato, quando tshark
                    # espone il campo BSSID.
                    if bssid and MAC_FULL.match(str(bssid).lower()):
                        if _fbssid and _fbssid != str(bssid).lower():
                            continue

                    _candidate = ""
                    _direction = ""
                    if _fromds and not _tods:
                        _candidate = _sa       # sorgente sul Distribution System
                        _direction = "FROMDS"
                    elif _tods and not _fromds:
                        _candidate = _da       # destinazione sul Distribution System
                        _direction = "TODS"

                    if not MAC_FULL.match(_candidate):
                        continue
                    if self.is_multicast_or_broadcast(_candidate):
                        continue
                    if _candidate in _nvr_infrastructure:
                        continue
                    if _candidate == str(bssid or "").lower():
                        continue

                    _r = direct_ds.setdefault(_candidate, {
                        "hits": 0, "fromds": 0, "tods": 0,
                        "bytes": 0, "first": None, "last": None
                    })
                    _r["hits"] += 1
                    _r["fromds" if _direction == "FROMDS" else "tods"] += 1
                    _r["bytes"] += max(0, _flen)
                    if _ts > 0:
                        _r["first"] = _ts if _r["first"] is None else min(_r["first"], _ts)
                        _r["last"] = _ts if _r["last"] is None else max(_r["last"], _ts)

                # Integra nel details_map senza dipendere dal filtro LAN.
                _radio = set(getattr(self, "wifi_radio_macs_session", set()) or set())
                _cache = load_vendor_cache()
                for _mac, _st in direct_ds.items():
                    if _mac in _radio:
                        continue
                    _d = dict(details_map.get(_mac, {}) or {})
                    _vendor = str(_d.get("vendor", "") or _cache.get(_mac, "") or "").strip()
                    if not _vendor:
                        try:
                            _vendor = str(self.resolve_mac_with_manuf(_mac) or "").strip()
                        except Exception:
                            _vendor = ""
                    if _vendor in ("Sconosciuto", "Unknown", "MAC locale/randomizzato"):
                        _vendor = ""
                    _dur = 0.0
                    if _st.get("first") is not None and _st.get("last") is not None:
                        _dur = max(0.0, float(_st["last"]) - float(_st["first"]))
                    _d.update({
                        "mac": _mac,
                        "vendor": _vendor,
                        "class": "LAN",
                        "direct_dvr_ds_hits": int(_st["hits"]),
                        "direct_dvr_fromds": int(_st["fromds"]),
                        "direct_dvr_tods": int(_st["tods"]),
                        "direct_dvr_bytes": int(_st["bytes"]),
                        "direct_dvr_duration": _dur,
                    })
                    details_map[_mac] = _d
            except Exception as _e:
                self.logmsg(
                    ("Direct NVR PCAP analysis error: " if is_en
                     else "Errore analisi diretta PCAP NVR: ") + str(_e)
                )

        for mac, det0 in details_map.items():
            det = dict(det0 or {})
            mac = str(mac or "").lower()
            if not MAC_FULL.match(mac):
                continue

            vendor = str(det.get("vendor", "") or "").strip()
            vlow = vendor.lower()
            if _looks_like_router_interface(mac, vendor):
                try:
                    self.command_debug_write(
                        f"[NVR] ESCLUSO INFRASTRUTTURA ROUTER/AP: {mac} {vendor} "
                        f"(BSSID/interfaccia CPE adiacente)"
                    )
                except Exception:
                    pass
                continue
            score = 0
            reasons = []

            # Vendor CCTV = indizio, non prova.
            cctv_vendor = any(x in vlow for x in (
                "dahua", "hikvision", "uniview", "unv", "axis",
                "hanwha", "wisenet", "vivotek", "reolink",
                "amcrest", "lorex", "avigilon", "bosch security",
                "shenzhen kean digital", "annke", "sannce"
            ))
            if cctv_vendor:
                score += 18
                reasons.append("CCTV/security vendor" if is_en else "vendor videosorveglianza")

            # Recupera le metriche se il MAC è già stato osservato anche dal
            # motore camera. È solo LETTURA: nessuna formula camera viene cambiata.
            cam_det = (getattr(self, "camera_candidate_details", {}) or {}).get(mac, {}) or {}
            duration = float(cam_det.get("duration", 0) or 0)
            frames = int(cam_det.get("frames", 0) or 0)
            tx = int(cam_det.get("tx_bytes", 0) or 0)
            rx = int(cam_det.get("rx_bytes", 0) or 0)
            bitrate = float(cam_det.get("bitrate", 0) or 0)
            total = tx + rx

            direct_hits = int(det.get("direct_dvr_ds_hits", 0) or 0)
            direct_fromds = int(det.get("direct_dvr_fromds", 0) or 0)
            direct_tods = int(det.get("direct_dvr_tods", 0) or 0)
            direct_bytes = int(det.get("direct_dvr_bytes", 0) or 0)
            direct_duration = float(det.get("direct_dvr_duration", 0) or 0)

            evidence_s = str(det.get("evidence", "") or "")
            notes_s = str(det.get("notes", "") or "")
            import re as _re_dvr
            _m_ds = _re_dvr.search(r"(?:DS indicators=|evidenze=)(\\d+)", notes_s, _re_dvr.I)
            ds_hits = int(_m_ds.group(1)) if _m_ds else 0
            if ds_hits <= 0:
                _m_parts = _re_dvr.findall(
                    r"(?:FromDS-Addr3-SRC|ToDS-Addr3-DST|WDS-Addr4-SRC|WDS-Addr3-DST)\\s+(\\d+)",
                    evidence_s, _re_dvr.I
                )
                ds_hits = sum(int(x) for x in _m_parts) if _m_parts else 0
            ds_hits = max(ds_hits, direct_hits)

            # Vendor specifico di videosorveglianza + presenza reale lato DS:
            # utile per recorder estremamente silenziosi. Non è una prova certa,
            # quindi produce soltanto "POSSIBILE NVR".
            recorder_capable_vendor = any(x in vlow for x in (
                "hikvision", "dahua", "uniview", "unv", "hanwha", "wisenet",
                "reolink", "amcrest", "lorex", "avigilon",
                "shenzhen kean digital", "annke", "sannce"
            ))
            sparse_recorder_hint = bool(
                recorder_capable_vendor
                and ds_hits >= 1
                and "LAN" in str(det.get("class", "LAN")).upper()
                and mac not in set(getattr(self, "wifi_radio_macs_session", set()) or set())
            )
            if sparse_recorder_hint:
                score += 34
                reasons.append(
                    "recorder-capable CCTV vendor + direct DS presence"
                    if is_en else
                    "vendor CCTV con prodotti recorder + presenza DS diretta"
                )
                if direct_hits >= 2:
                    score += 6
                if direct_hits >= 4:
                    score += 6
                if direct_duration >= 30:
                    score += 5
                if direct_fromds > 0 and direct_tods > 0:
                    score += 8
                    reasons.append(
                        "bidirectional DS evidence"
                        if is_en else "evidenza DS bidirezionale"
                    )

            if duration >= 60:
                score += 18
                reasons.append("persistent presence" if is_en else "presenza persistente")
            elif duration >= 25:
                score += 8

            if total >= 8_000_000:
                score += 22
                reasons.append("high aggregate traffic" if is_en else "traffico aggregato elevato")
            elif total >= 2_000_000:
                score += 12

            if frames >= 2500:
                score += 18
                reasons.append("many data frames" if is_en else "molti frame dati")
            elif frames >= 700:
                score += 9

            if bitrate >= 1.5:
                score += 14
                reasons.append("sustained stream" if is_en else "flusso sostenuto")
            elif bitrate >= 0.4:
                score += 7

            if tx > 0 and rx > 0:
                balance = min(tx, rx) / max(tx, rx)
                if balance >= 0.08:
                    score += 8
                    reasons.append("bidirectional aggregate traffic" if is_en else "traffico aggregato bidirezionale")

            # Firma NVR LAN: un recorder puo' essere visibile come endpoint DS
            # destinatario di molti frame ToDS (camera Wi-Fi -> NVR LAN) oppure
            # come endpoint aggregato bidirezionale durante live-view/cloud.
            nvr_sink_signature = bool(
                direct_tods >= 20
                and direct_hits >= 30
                and direct_duration >= 20
                and direct_bytes >= 250000
            )
            nvr_aggregate_signature = bool(
                duration >= 30
                and frames >= 350
                and total >= 1000000
                and bitrate >= 0.20
                and tx > 0 and rx > 0
            )
            if nvr_sink_signature:
                score += 18
                reasons.append(
                    "LAN NVR sink: sustained camera-to-recorder DS traffic"
                    if is_en else "NVR LAN ricevente: traffico camera->recorder sostenuto sul DS"
                )
            if nvr_aggregate_signature:
                score += 12
                reasons.append(
                    "aggregate recorder/live-view traffic signature"
                    if is_en else "firma traffico aggregato recorder/live-view"
                )

            # NVR: niente classificazione dal solo OUI. Servono DS reale +
            # traffico da recorder, oppure vendor recorder + piu' evidenze coerenti.
            behavioral = score - (18 if cctv_vendor else 0)
            moderate_nvr = bool(
                nvr_sink_signature
                or nvr_aggregate_signature
                or sparse_recorder_hint
                or (recorder_capable_vendor and ds_hits >= 3
                    and (direct_duration >= 15 or direct_hits >= 8)
                    and (direct_fromds > 0 or direct_tods > 0))
            )
            if not moderate_nvr:
                continue

            if sparse_recorder_hint:
                score = max(score, 48)
            if nvr_sink_signature:
                score = max(score, 52)
            elif nvr_aggregate_signature:
                score = max(score, 46)
            elif behavioral < 25:
                # Vendor recorder + DS, ma firma ancora debole: solo osservazione.
                score = max(36, min(score, 41))

            score = min(100, score)
            if score >= 80:
                level = "HIGHLY LIKELY NVR" if is_en else "NVR MOLTO PROBABILE"
            elif score >= 62:
                level = "LIKELY NVR" if is_en else "NVR PROBABILE"
            elif score >= 42:
                level = "POSSIBLE NVR" if is_en else "POSSIBILE NVR"
            else:
                level = "LOW CONFIDENCE NVR" if is_en else "NVR DA OSSERVARE"
            txrx = f"{tx/1048576:.1f}/{rx/1048576:.1f} MB"
            dur = f"{duration:.0f} s"
            indicators = "; ".join(reasons[:8])

            # Dettagli separati, marcati esplicitamente DVR/NVR.
            dvr_detail = dict(cam_det) if cam_det else dict(det)
            dvr_detail.update({
                "mac": mac,
                "vendor": vendor,
                "score": score,
                "level": level,
                "confidence": score,
                "class": "NVR",
                "provenance": "LAN",
                "reasons": reasons,
                "dvr_nvr_separate_algorithm": True,
                "nvr_candidate": True,
                "source_display": "LAN NVR",
                "traffic_profile": (
                    "NVR LAN CAMERA-SINK" if nvr_sink_signature else
                    "NVR AGGREGATE/CLOUD" if nvr_aggregate_signature else
                    "NVR RECORDER-COMPATIBLE"
                ),
            })
            # Scheda DETTAGLI completa anche per NVR sparsi.
            dvr_detail["details_extra"] = {
                "device_type": level,
                "source": "LAN",
                "nvr_score": score,
                "indicators": indicators,
                "ds_hits": int(det.get("direct_dvr_ds_hits", 0) or 0),
                "fromds": int(det.get("direct_dvr_fromds", 0) or 0),
                "tods": int(det.get("direct_dvr_tods", 0) or 0),
                "observed_bytes": int(det.get("direct_dvr_bytes", 0) or 0),
                "observed_duration": float(det.get("direct_dvr_duration", 0) or 0),
            }
            self.camera_candidate_details[mac] = dvr_detail
            result.append((
                mac, vendor, f"{score}/100", level,
                txrx, "LAN", dur, indicators
            ))

        return result

    def analyze_camera_candidates(self, cap, bssid, observed_rows=None):
        is_en = getattr(self,"language","it") == "en"
        """
        Motore multi-segnale per classificare passivamente dispositivi compatibili
        con telecamere/video-IoT. Lavora anche quando il payload 802.11 e' cifrato:
        in quel caso usa direzione, volume, durata, burst, periodicita', dimensione
        frame e metadati radio disponibili. IP, porte e protocolli applicativi non
        partecipano alla valutazione: la cattura viene considerata cifrata.

        IMPORTANTE: il risultato e' probabilistico. Uno score elevato indica che il
        comportamento osservato e' compatibile con una telecamera, non una prova.
        """
        if not cap or not Path(cap).exists():
            return []
        bssid=(bssid or "").strip().lower()
        if not MAC_FULL.match(bssid):
            return []
        infrastructure_bssids = set(self._known_ap_bssids())
        infrastructure_bssids.add(bssid)

        vendors={}
        classes={}
        for row in observed_rows or []:
            if len(row) >= 3:
                mac=str(row[0]).lower()
                vendors[mac]=str(row[1] or "Sconosciuto")
                classes[mac]=str(row[2] or "")

        # Interroga una sola volta il catalogo campi della versione tshark presente.
        if self._tshark_fields_cache is None:
            catalog=run(["tshark","-G","fields"], timeout=10)
            available=set()
            if catalog.returncode == 0:
                for line in catalog.stdout.splitlines():
                    cols=line.split("\t")
                    if len(cols)>2 and cols[0] == "F":
                        available.add(cols[2].strip())
            self._tshark_fields_cache=available
        available=self._tshark_fields_cache or set()

        # Tutti i segnali potenzialmente utili. I campi non supportati dalla build
        # installata vengono automaticamente ignorati.
        candidates=[
            "frame.time_epoch","frame.len","frame.protocols",
            "wlan.fc.type","wlan.fc.subtype","wlan.fc.retry","wlan.fc.tods","wlan.fc.fromds",
            "wlan.sa","wlan.da","wlan.ta","wlan.ra","wlan.bssid","wlan.qos.tid",
            "radiotap.dbm_antsignal","radiotap.datarate","radiotap.data_retries",
            "ip.src","ip.dst","ipv6.src","ipv6.dst","ip.proto",
            "tcp.srcport","tcp.dstport","udp.srcport","udp.dstport",
            "dns.qry.name","dns.resp.name","dhcp.option.hostname","bootp.option.hostname",
            "http.host","http.request.uri","http.user_agent",
            "tls.handshake.extensions_server_name",
            "rtsp.request","rtsp.response","rtp.ssrc","rtcp.ssrc",
            "ssdp.http.request.method","ssdp.st","ssdp.usn","ssdp.location",
            "mdns.dns.qry.name","mdns.dns.resp.name",
            "mqtt.topic","coap.opt.uri_path"
        ]
        fields=[f for f in candidates if (not available or f in available)]
        mandatory=[f for f in (
            "frame.time_epoch","frame.len","wlan.sa","wlan.da","wlan.ta","wlan.ra","wlan.bssid"
        ) if f in fields]
        if len(mandatory) < 5:
            return []

        cmd=["tshark","-r",str(cap),"-T","fields","-E","separator=/t","-E","occurrence=f"]
        for f in fields:
            cmd.extend(["-e",f])
        p=run(cmd, timeout=20)
        if p.returncode != 0 and not (p.stdout or "").strip():
            self.logmsg("Analisi possibili telecamere fallita: " + (p.stderr or "errore tshark"))
            return []

        stats={}
        def first(v): return (v or "").split(",",1)[0].strip()
        def values(v): return [x.strip() for x in (v or "").split(",") if x.strip()]
        def as_int(v):
            try: return int(float(first(v)))
            except Exception: return 0
        def as_float(v):
            try: return float(first(v))
            except Exception: return 0.0
        def one_mac(v):
            m=MAC_FIND.search(v or "")
            return m.group(0).lower() if m else ""
        def get(mac):
            return stats.setdefault(mac, {
                "first":None,"last":None,"frames":0,"bytes":0,
                "tx_frames":0,"rx_frames":0,"tx_bytes":0,"rx_bytes":0,
                "large":0,"small":0,"medium":0,"times":[],"tx_times":[],"rx_times":[],
                "lengths":[],"ports":set(),"names":set(),"proto":set(),"uris":set(),
                "retry":0,"data_frames":0,"qos_tids":set(),
                 "signals":[],"phy_rates":[],"radio_retries":[],
                "seconds":{},"tx_seconds":{},"rx_seconds":{},
                "useful_frames":0,"useful_tx_bytes":0,"useful_rx_bytes":0,
                "useful_lengths":[],"useful_large":0,"useful_small":0,
                "useful_seconds":{},"useful_tx_seconds":{},
                "null_frames":0,"null_tx_frames":0,"null_rx_frames":0
            })

        idx={name:i for i,name in enumerate(fields)}
        capture_first=None; capture_last=None
        for line in p.stdout.splitlines():
            vals=line.split("\t")
            vals += [""]*(len(fields)-len(vals))
            row={f:vals[i] for f,i in idx.items()}
            ts=as_float(row.get("frame.time_epoch"))
            flen=max(0,as_int(row.get("frame.len")))
            sa=one_mac(row.get("wlan.sa")); da=one_mac(row.get("wlan.da"))
            ta=one_mac(row.get("wlan.ta")); ra=one_mac(row.get("wlan.ra")); fb=one_mac(row.get("wlan.bssid"))
            if bssid not in (fb,ta,ra,sa,da):
                continue

            # In un PCAP unificato con scansioni consequenziali, la durata di
            # riferimento deve appartenere SOLO al BSSID che stiamo analizzando.
            # Se includiamo anche la prima/seconda scansione di altri BSSID, la
            # presenza relativa dei client della TAVERNA (o di qualunque altro AP)
            # viene artificialmente abbassata e una camera idle puo' sparire.
            if ts:
                capture_first=ts if capture_first is None else min(capture_first,ts)
                capture_last=ts if capture_last is None else max(capture_last,ts)

            mac=""; direction=""
            tods=as_int(row.get("wlan.fc.tods")) == 1
            fromds=as_int(row.get("wlan.fc.fromds")) == 1
            if tods and not fromds:
                mac=ta or sa; direction="tx"
            elif fromds and not tods:
                mac=ra or da; direction="rx"
            elif ra == bssid and ta and ta != bssid:
                mac=ta; direction="tx"
            elif ta == bssid and ra and ra != bssid:
                mac=ra; direction="rx"
            elif da == bssid and sa and sa != bssid:
                mac=sa; direction="tx"
            elif sa == bssid and da and da != bssid:
                mac=da; direction="rx"
            if (
                not mac or mac == bssid or mac in infrastructure_bssids
                or not MAC_FULL.match(mac) or self.is_multicast_or_broadcast(mac)
            ):
                continue

            st=get(mac)
            st["frames"] += 1; st["bytes"] += flen
            st["lengths"].append(flen)
            if flen >= 1000: st["large"] += 1
            elif flen <= 300: st["small"] += 1
            else: st["medium"] += 1

            if ts:
                st["times"].append(ts)
                st["first"] = ts if st["first"] is None else min(st["first"],ts)
                st["last"] = ts if st["last"] is None else max(st["last"],ts)
                sec=int(ts)
                st["seconds"][sec]=st["seconds"].get(sec,0)+flen
                if direction == "tx":
                    st["tx_times"].append(ts); st["tx_seconds"][sec]=st["tx_seconds"].get(sec,0)+flen
                elif direction == "rx":
                    st["rx_times"].append(ts); st["rx_seconds"][sec]=st["rx_seconds"].get(sec,0)+flen

            if direction == "tx":
                st["tx_frames"] += 1; st["tx_bytes"] += flen
            elif direction == "rx":
                st["rx_frames"] += 1; st["rx_bytes"] += flen

            is_data=as_int(row.get("wlan.fc.type")) == 2
            data_subtype=as_int(row.get("wlan.fc.subtype"))
            is_null_data=bool(is_data and data_subtype in (4,12))
            is_retry=bool(as_int(row.get("wlan.fc.retry")))

            if is_null_data:
                st["null_frames"] += 1
                if direction == "tx":
                    st["null_tx_frames"] += 1
                elif direction == "rx":
                    st["null_rx_frames"] += 1

            if is_data:
                st["data_frames"] += 1
                if not is_retry:
                    st["useful_frames"] += 1
                    st["useful_lengths"].append(flen)
                    if flen>=1000: st["useful_large"] += 1
                    elif flen<=300: st["useful_small"] += 1
                    if direction=="tx": st["useful_tx_bytes"] += flen
                    elif direction=="rx": st["useful_rx_bytes"] += flen
                    if ts:
                        sec=int(ts)
                        st["useful_seconds"][sec]=st["useful_seconds"].get(sec,0)+flen
                        if direction=="tx":
                            st["useful_tx_seconds"][sec]=st["useful_tx_seconds"].get(sec,0)+flen
            if is_retry:
                st["retry"] += 1
            q=first(row.get("wlan.qos.tid"))
            if q.isdigit(): st["qos_tids"].add(int(q))
            sig=as_float(row.get("radiotap.dbm_antsignal"))
            if sig: st["signals"].append(sig)
            rate=as_float(row.get("radiotap.datarate"))
            if rate>0: st["phy_rates"].append(rate)
            rr=as_int(row.get("radiotap.data_retries"))
            if rr>0: st["radio_retries"].append(rr)

            for f in ("tcp.srcport","tcp.dstport","udp.srcport","udp.dstport"):
                for v in values(row.get(f)):
                    if v.isdigit(): st["ports"].add(int(v))
            for f in (
                "dns.qry.name","dns.resp.name","dhcp.option.hostname","bootp.option.hostname",
                "http.host","tls.handshake.extensions_server_name",
                "ssdp.st","ssdp.usn","ssdp.location","mdns.dns.qry.name","mdns.dns.resp.name"
            ):
                for v in values(row.get(f)):
                    v=v.lower()
                    if v: st["names"].add(v[:180])
            for f in ("http.request.uri","mqtt.topic","coap.opt.uri_path"):
                for v in values(row.get(f)):
                    if v: st["uris"].add(v.lower()[:180])

            protocols=(first(row.get("frame.protocols")) or "").lower()
            if first(row.get("rtsp.request")) or first(row.get("rtsp.response")) or "rtsp" in protocols:
                st["proto"].add("RTSP")
            if first(row.get("rtp.ssrc")) or ":rtp" in protocols:
                st["proto"].add("RTP")
            if first(row.get("rtcp.ssrc")) or "rtcp" in protocols:
                st["proto"].add("RTCP")
            if first(row.get("ssdp.http.request.method")) or "ssdp" in protocols:
                st["proto"].add("SSDP")
            if "mdns" in protocols:
                st["proto"].add("mDNS")
            if "mqtt" in protocols or first(row.get("mqtt.topic")):
                st["proto"].add("MQTT")
            if "coap" in protocols or first(row.get("coap.opt.uri_path")):
                st["proto"].add("CoAP")
            if "quic" in protocols:
                st["proto"].add("QUIC")
            if "tls" in protocols:
                st["proto"].add("TLS")

        # Database euristico. Il vendor e' solo un indizio e non deve dominare lo score.
        camera_vendor_strong=(
            "hikvision","dahua","axis","vivotek","reolink","foscam","ezviz","imou",
            "arlo","wyze","ring","blink","amcrest","hanwha","wisenet","bosch security",
            "mobotix","avigilon","instar","lorex","swann","geovision","acti","xiongmai","xmeye"
        )
        camera_vendor_mixed=("ubiquiti","unifi","tapo","tp-link","eufy")
        iot_vendor_words=("tuya","espressif","realtek","ingenic","sonoff","silicon labs","azurewave","ampak","trolink","shenzhen trolink")
        consumer_vendor_words=(
            "apple","intel","lenovo","dell","hewlett","google","motorola","oneplus",
            "asustek","acer","microsoft"
        )
        tv_media_words=("roku","chromecast","amazon technologies","fire tv","nvidia","sony interactive")
        camera_name_words=(
            "camera","cam","ipc","ipcam","nvr","dvr","onvif","hikvision","dahua","reolink",
            "ezviz","imou","arlo","ring","wyze","tapo","vivotek","wisenet","amcrest","xmeye"
        )
        video_service_words=("netflix","youtube","googlevideo","twitch","spotify","primevideo","disney")
        camera_ports={554,8554,8000,8001,8080,8081,8899,3702,1935,5000,37777,34567,7070}
        discovery_ports={1900,5353,3702}
        iot_ports={5683,1883,8883,123}

        def mean(vals):
            return sum(vals)/len(vals) if vals else 0.0
        def coefficient_of_variation(vals):
            if len(vals)<2: return 99.0
            m=mean(vals)
            if m<=0: return 99.0
            var=sum((x-m)**2 for x in vals)/len(vals)
            return (var**0.5)/m
        def percentile(vals, pct):
            if not vals: return 0.0
            s=sorted(vals)
            pos=(len(s)-1)*pct
            lo=int(pos); hi=min(len(s)-1,lo+1); frac=pos-lo
            return s[lo]*(1-frac)+s[hi]*frac

        out=[]
        for mac,st in stats.items():
            if classes.get(mac) == "AP":
                continue
            # Via di mezzo: 5 frame sono il minimo per valutare una station.
            # Non basta essere associati al Wi-Fi per entrare tra le telecamere.
            if st["frames"] < 5:
                continue

            # Se il motore LAN ha già identificato questo MAC come endpoint LAN,
            # NON deve essere trattato anche come station Wi-Fi. Nei frame 802.11
            # SA/DA possono infatti essere indirizzi logici di host dietro AP/bridge.
            # Il MAC verrà eventualmente valutato dal motore telecamere LAN dedicato.
            _lan_details_all = getattr(self, "lan_candidate_details", {}) or {}
            # La prova radio diretta ha priorità sulla classificazione LAN:
            # un vero client associato al BSSID può comparire anche in Address3
            # e finire nei dettagli LAN per effetto del bridge/AP.
            _direct_wifi_client = (classes.get(mac) == "Wi-Fi ASSOCIATO")
            if mac in _lan_details_all and not _direct_wifi_client:
                continue

            vendor=vendors.get(mac,"Sconosciuto")
            if not vendor or vendor.lower() == "sconosciuto":
                resolved=self.resolve_mac_with_manuf(mac)
                if resolved not in ("Sconosciuto","MAC locale/randomizzato"):
                    vendor=resolved.split("_",1)[0]

            # Fallback OUI Trolink: alcuni database manuf installati su Kali
            # non contengono ancora tutti i blocchi del produttore. Non assegna
            # automaticamente la classe CAMERA: serve comunque la firma radio/
            # temporale verificata piu' avanti.
            _trolink_ouis = {
                "30:4a:26", "48:8f:4c", "4c:a3:8f", "68:b9:d3",
                "74:5e:a5", "94:a4:08", "cc:c4:b2", "dc:84:03",
                "f0:a8:82"
            }
            if mac[:8] in _trolink_ouis and (not vendor or vendor.lower() == "sconosciuto"):
                vendor = "Shenzhen Trolink Technology CO, LTD"
            vlow=vendor.lower()

            # Safety-net infrastruttura: router/AP e loro interfacce adiacenti
            # non possono essere classificati come telecamere Wi-Fi.
            try:
                if self._is_camera_infrastructure_mac(mac, vendor):
                    continue
            except Exception:
                pass

            # Anti-falso-positivo: MAC localmente amministrato/randomizzato.
            # Esempio reale della cattura: 2E:36:79:72:73:5B.
            # Un MAC di questo tipo non ha un OUI hardware affidabile e può essere
            # un client con privacy MAC. Non lo promuoviamo a telecamera in assenza
            # di un'identità camera forte e verificabile.
            try:
                _first_octet = int(mac.split(":", 1)[0], 16)
                locally_administered = bool(_first_octet & 0x02)
            except Exception:
                locally_administered = False

            duration=max(0.0,(st["last"] or 0)-(st["first"] or 0))
            tx=st["useful_tx_bytes"]; rx=st["useful_rx_bytes"]
            if st["useful_frames"]<3:
                tx=st["tx_bytes"]; rx=st["rx_bytes"]
            total=max(1,tx+rx)
            tx_ratio=tx/total
            bitrate=(total*8.0/duration/1_000_000.0) if duration >= 1 else 0.0
            tx_bitrate=(tx*8.0/duration/1_000_000.0) if duration >= 1 else 0.0
            useful_n=max(1,st["useful_frames"] or st["frames"])
            large_ratio=(st["useful_large"] if st["useful_frames"] else st["large"])/useful_n
            small_ratio=(st["useful_small"] if st["useful_frames"] else st["small"])/useful_n
            retry_ratio=st["retry"]/max(1,st["data_frames"])

            # Continuita': percentuale di secondi della sessione in cui il client e' attivo.
            session_secs=max(1,int(duration)+1)
            active_map=st["useful_seconds"] or st["seconds"]
            tx_map=st["useful_tx_seconds"] or st["tx_seconds"]
            active_secs=len(active_map)
            activity_ratio=min(1.0,active_secs/session_secs)
            tx_activity=min(1.0,len(tx_map)/session_secs)
            capture_duration=max(0.0,(capture_last or 0)-(capture_first or 0))
            presence_ratio_capture=min(1.0,active_secs/max(1,int(capture_duration)+1))

            sec_rates=[b*8/1_000_000.0 for b in active_map.values()]
            tx_sec_rates=[b*8/1_000_000.0 for b in tx_map.values()]
            p95_rate=percentile(sec_rates,0.95)
            p95_tx_rate=percentile(tx_sec_rates,0.95)
            burst_cv=coefficient_of_variation(sec_rates)
            tx_rate_cv=coefficient_of_variation(tx_sec_rates)

            times=sorted(st["times"])
            gaps=[b-a for a,b in zip(times,times[1:]) if 0 < b-a <= 30]
            gap_cv=coefficient_of_variation(gaps) if len(gaps)>=10 else 99.0
            gap_mean=mean(gaps)

            names=" ".join(sorted(st["names"]))
            uris=" ".join(sorted(st["uris"]))
            cam_hits=sorted(st["ports"] & camera_ports)
            discovery_hits=sorted(st["ports"] & discovery_ports)
            iot_hits=sorted(st["ports"] & iot_ports)

            # CATEGORIA 1: identita' / vendor (max 20)
            identity=0; reasons=[]
            if any(w in vlow for w in camera_vendor_strong):
                identity=20; reasons.append("camera-oriented vendor/OUI" if is_en else "vendor camera")
            elif any(w in vlow for w in camera_vendor_mixed):
                identity=10; reasons.append("vendor with camera product line" if is_en else "vendor con linea telecamere")
            elif any(w in vlow for w in iot_vendor_words):
                identity=8
                if "trolink" in vlow:
                    reasons.append(
                        "embedded Wi-Fi module/vendor also used in IP-camera hardware"
                        if is_en else
                        "vendor/modulo Wi-Fi embedded usato anche in hardware IP-camera"
                    )
                else:
                    reasons.append("IoT-oriented vendor/OUI" if is_en else "vendor IoT")
            elif any(w in vlow for w in consumer_vendor_words):
                identity=-8; reasons.append("generic client-device vendor" if is_en else "vendor client generico")
            elif any(w in vlow for w in tv_media_words):
                identity=-6; reasons.append("media/TV-device vendor" if is_en else "vendor media/TV")

            # Un MAC locale/randomizzato NON viene più escluso a priori.
            # Alcuni dispositivi embedded possono usare MAC software/locali.
            # Verrà però accettato solo con una firma comportamentale molto forte
            # (controllo applicato più avanti), così telefoni/PC con privacy MAC
            # non diventano automaticamente possibili telecamere.

            # Nessuna valutazione applicativa: IP/porte/protocolli non sono usati.
            protocol=0

            # CATEGORIA 3: comportamento di upload tipico di una camera (max 23)
            direction=0
            if duration>=20 and tx>=250000:
                if tx_ratio>=0.80 and tx_bitrate>=0.15:
                    direction=23; reasons.append("video-like uplink dominance" if is_en else "upload video prevalente")
                elif tx_ratio>=0.65 and tx_bitrate>=0.08:
                    direction=17; reasons.append("uplink-dominant traffic" if is_en else "upload prevalente")
                elif tx_ratio>=0.55:
                    direction=9; reasons.append("TX>RX")

            # CATEGORIA 4: continuita' e flusso sostenuto (max 18)
            continuity=0
            if duration>=60 and activity_ratio>=0.70 and st["frames"]>=180:
                continuity=18; reasons.append("continuous traffic flow" if is_en else "flusso continuo")
            elif duration>=30 and activity_ratio>=0.50 and st["frames"]>=100:
                continuity=13; reasons.append("sustained traffic" if is_en else "traffico sostenuto")
            elif duration>=12 and activity_ratio>=0.35 and st["frames"]>=40:
                continuity=7; reasons.append("persistent session" if is_en else "sessione persistente")
            if duration>=30 and len(tx_sec_rates)>=12 and tx_activity>=0.45:
                if tx_rate_cv<0.75:
                    continuity=min(18,continuity+4)
                    reasons.append("steady uplink throughput" if is_en else "throughput upload regolare")
                elif tx_rate_cv<1.20:
                    continuity=min(18,continuity+2)

            # CATEGORIA 5: forma del traffico / frame (max 15)
            shape=0
            if large_ratio>=0.55 and st["frames"]>=60:
                shape += 7; reasons.append("high proportion of large frames" if is_en else "molti frame grandi")
            elif large_ratio>=0.35 and st["frames"]>=50:
                shape += 4
            if bitrate>=0.40 or p95_rate>=1.0:
                shape += 6; reasons.append(f"{bitrate:.2f} Mbps")
            elif bitrate>=0.12:
                shape += 3
            if tx_activity>=0.45 and p95_tx_rate>=0.20:
                shape += 2
            shape=min(15,shape)

            # CATEGORIA 6: regolarita'/IoT (max 10). Non premia troppo per evitare
            # di confondere heartbeat di sensori con video.
            temporal=0
            if len(gaps)>=20 and gap_mean>0:
                if gap_cv<0.55:
                    temporal=6; reasons.append("regular timing pattern" if is_en else "temporizzazione regolare")
                elif gap_cv<0.90:
                    temporal=3

            # Bonus radio minimo: serve solo come indicatore di dispositivo fisso/stabile,
            # mai come prova di telecamera.
            radio=0
            if len(st["signals"])>=20:
                sig_cv=coefficient_of_variation([abs(x) for x in st["signals"] if x])
                sig_range=(max(st["signals"])-min(st["signals"])) if st["signals"] else 99
                if sig_range<=8 and sig_cv<0.12 and duration>=30:
                    radio=3; reasons.append("stable RF signal" if is_en else "segnale stabile")

            # Penalita' anti-falso-positivo.
            penalty=0
            if rx > tx*3 and bitrate>=0.5:
                penalty += 15; reasons.append("download-dominant traffic" if is_en else "download dominante")
            if burst_cv>2.2 and activity_ratio<0.30 and duration>=20:
                penalty += 10; reasons.append("bursty traffic" if is_en else "traffico a burst")
            if duration<8:
                penalty += 8
            if small_ratio>0.80 and bitrate<0.08:
                penalty += 8; reasons.append("small-frame-only pattern" if is_en else "solo piccoli pacchetti")
            if any(w in vlow for w in consumer_vendor_words) and tx_ratio<0.45:
                penalty += 8; reasons.append("consumer/download-oriented profile" if is_en else "profilo consumer/download")
            if retry_ratio>=0.45 and st["data_frames"]>=40:
                penalty += 6; reasons.append("high retry rate" if is_en else "molte ritrasmissioni")
            elif retry_ratio>=0.25 and st["data_frames"]>=40:
                penalty += 3

            # Bonus prudente per un client Wi-Fi realmente associato e con presenza
            # osservata nel tempo. Non identifica una camera, ma evita di perdere
            # dispositivi fissi/IoT a basso traffico (tipico delle camera idle).
            presence=0
            if classes.get(mac) == "Wi-Fi ASSOCIATO":
                if duration >= 20 and st["frames"] >= 25:
                    presence += 2
                if duration >= 45 and tx_ratio >= 0.50:
                    presence += 2
                if len(st["signals"]) >= 15:
                    sig_range=(max(st["signals"])-min(st["signals"])) if st["signals"] else 99
                    if sig_range <= 10:
                        presence += 2
                if tx_activity >= 0.20 and duration >= 30:
                    presence += 2
                if capture_duration>=30 and presence_ratio_capture>=0.55:
                    presence += 2
            presence=min(8,presence)
            if presence >= 4:
                reasons.append("stable Wi-Fi presence" if is_en else "presenza Wi-Fi stabile")

            raw=identity+direction+continuity+shape+temporal+radio+presence-penalty

            # Confidenza descrive QUANTO materiale abbiamo osservato, ma non deve
            # moltiplicare brutalmente lo score: nella versione precedente una camera
            # di vendor noto poteva sparire solo perche' quasi inattiva.
            coverage=0
            if duration>=15: coverage += 1
            if duration>=45: coverage += 1
            if st["frames"]>=50: coverage += 1
            if st["frames"]>=150: coverage += 1
            if len(st["signals"])>=15 or len(gaps)>=20: coverage += 1
            confidence=min(1.0,0.45+coverage*0.11)

            # Penalita' di incertezza limitata: riduce i punteggi con poche evidenze
            # senza cancellare gli indizi forti di identita'/protocollo.
            uncertainty_penalty = 0
            if coverage <= 1:
                uncertainty_penalty = 10
            elif coverage == 2:
                uncertainty_penalty = 6
            elif coverage == 3:
                uncertainty_penalty = 3
            score=int(round(max(0,min(100,raw-uncertainty_penalty))))

            # Il vendor camera e' solo un indizio: da solo non basta per una classe alta.
            if identity>=20:
                score=max(score,42)
                if direction < 9 and continuity < 7 and shape < 4:
                    score=min(score,61)
            elif identity==10 and direction<9 and continuity<7 and shape<4:
                score=min(score,41)
            score=max(0,min(100,score))

            # PROFILI DI TRAFFICO CAMERA (solo metadati 802.11, utili anche con payload cifrato).
            # CLOUD STREAMING: una camera cloud tende ad avere un uplink persistente,
            # distribuito nel tempo, con bitrate/raffiche coerenti e una quota non
            # trascurabile di frame grandi. Non basta il solo TX>RX.
            cloud_stream_strong = bool(
                duration >= 35
                and st["useful_frames"] >= 120
                and tx_ratio >= 0.72
                and tx_bitrate >= 0.10
                and activity_ratio >= 0.45
                and tx_activity >= 0.40
                and (large_ratio >= 0.25 or p95_tx_rate >= 0.35)
                and retry_ratio < 0.40
            )
            cloud_stream_very_strong = bool(
                duration >= 45
                and st["useful_frames"] >= 180
                and tx_ratio >= 0.80
                and tx_bitrate >= 0.18
                and activity_ratio >= 0.55
                and tx_activity >= 0.50
                and (large_ratio >= 0.35 or p95_tx_rate >= 0.55)
                and retry_ratio < 0.35
            )
            if cloud_stream_very_strong:
                score = min(100, score + 8)
                reasons.append(
                    "strong camera-cloud uplink streaming signature"
                    if is_en else "forte firma streaming uplink camera-cloud"
                )
            elif cloud_stream_strong:
                score = min(100, score + 4)
                reasons.append(
                    "camera-cloud uplink streaming signature"
                    if is_en else "firma streaming uplink camera-cloud"
                )

            # Firma "camera Wi-Fi inattiva / basso traffico".
            # Una camera collegata ma non osservata in live-view può inviare solo
            # keepalive, telemetria e piccoli pacchetti cloud: bitrate e frame grandi
            # diventano quindi indicatori troppo severi.
            #
            # Richiediamo invece:
            # - associazione diretta al BSSID per una sessione lunga;
            # - molti frame TX e attività distribuita nel tempo;
            # - TX prevalente;
            # - vendor/modulo embedded-IoT come indizio debole.
            # Firma adattiva per camera Wi-Fi idle/persistente.
            #
            # La vecchia soglia (>=300 frame e >=180 TX) era troppo rigida:
            # una camera collegata al cloud ma senza live-view può restare presente
            # per quasi tutta la cattura inviando circa un pacchetto al secondo.
            #
            # Usiamo quindi anche la PERSISTENZA relativa alla durata della cattura,
            # non soltanto il numero assoluto di frame.
            min_persistent_frames = max(55, int(max(1.0, capture_duration) * 0.45))
            min_persistent_tx = max(40, int(max(1.0, capture_duration) * 0.32))

            low_traffic_wifi_camera = bool(
                identity >= 20
                and duration >= 45
                and capture_duration >= 45
                and presence_ratio_capture >= 0.55
                and st["tx_frames"] >= min_persistent_tx
                and st["frames"] >= min_persistent_frames
                and tx_ratio >= 0.60
                and small_ratio >= 0.40
            )

            # Variante ancora più caratteristica di dispositivo fisso embedded:
            # presenza molto lunga, TX prevalente e quasi solo piccoli keepalive.
            # Richiede comunque un indizio vendor IoT/camera, quindi non basta
            # il solo comportamento per promuovere telefoni/PC.
            persistent_embedded_idle = bool(
                identity >= 20
                and duration >= 60
                and capture_duration >= 60
                and presence_ratio_capture >= 0.70
                and st["tx_frames"] >= 45
                and st["frames"] >= 70
                and tx_ratio >= 0.65
                and small_ratio >= 0.75
            )

            # Firma "idle sparsa": alcune IP-camera, quando nessuno guarda il live,
            # non trasmettono ogni secondo. Restano associate per quasi tutta la
            # cattura ma inviano keepalive/cloud a intervalli. La vecchia richiesta
            # presence_ratio>=0.70 le eliminava.
            #
            # Per evitare telefoni/PC richiediamo comunque:
            # - vendor/modulo embedded-IoT (identity >= 8);
            # - MAC globale, non privacy/randomizzato;
            # - sessione molto lunga;
            # - almeno 80 frame e 60 TX;
            # - quasi esclusivamente frame piccoli;
            # - TX almeno leggermente prevalente;
            # - retry non elevato.
            sparse_embedded_idle = bool(
                identity >= 20
                and not locally_administered
                and duration >= 90
                and capture_duration >= 90
                and presence_ratio_capture >= 0.12
                and st["tx_frames"] >= 60
                and st["frames"] >= 80
                and tx_ratio >= 0.50
                and small_ratio >= 0.90
                and retry_ratio < 0.25
            )

            # Firma Trolink idle/persistente.
            # Nella cattura reale TAVERNA una camera Trolink resta associata per
            # quasi tutta la sessione ma scambia soprattutto piccoli keepalive
            # bidirezionali: per questo TX/RX puo' essere vicino a 50/50 e non
            # raggiungere le vecchie soglie da streaming attivo.
            #
            # Il solo OUI NON basta: richiediamo MAC globale, sessione lunga,
            # molti frame, prevalenza TX almeno moderata, quasi soli frame piccoli
            # e retry contenuto. In questo modo entra come POSSIBILE camera idle,
            # non come identificazione certa.
            # Soglie adattive Trolink idle.
            #
            # Le catture reali mostrano che una camera Trolink collegata al cloud ma
            # senza live-view puo' restare associata per quasi tutta la sessione
            # scambiando soprattutto NULL/keepalive e pochi DATA cifrati. In quel
            # caso il numero di "useful_frames" e la percentuale di secondi attivi
            # possono essere bassi anche se il dispositivo e' realmente presente.
            #
            # Per evitare di riaprire i falsi positivi generici, questa eccezione
            # resta limitata a OUI/vendor Trolink + MAC globale + lunga permanenza
            # sul BSSID + piccoli frame + TX consistente + retry contenuto.
            _trolink_min_useful = max(60, int(max(1.0, capture_duration) * 0.50))
            _trolink_min_tx = max(45, int(max(1.0, capture_duration) * 0.35))
            _trolink_span_ratio = (
                duration / max(1.0, capture_duration)
                if capture_duration > 0 else 0.0
            )
            embedded_camera_exception = bool(
                identity == 8
                and "trolink" in vlow
                and not locally_administered
                and duration >= 60
                and capture_duration >= 60
                and _trolink_span_ratio >= 0.65
                and st["useful_frames"] >= _trolink_min_useful
                and st["tx_frames"] >= _trolink_min_tx
                and tx_ratio >= 0.45
                and small_ratio >= 0.90
                and presence_ratio_capture >= 0.12
                and activity_ratio >= 0.14
                and retry_ratio < 0.30
            )

            # Caso reale TAVERNA:
            # alcune telecamere Trolink completamente idle non scambiano payload
            # durante la finestra osservata, ma rimangono associate inviando NULL
            # DATA / QoS NULL keepalive. Questo NON dimostra streaming, ma con:
            #   - OUI/vendor Trolink verificabile;
            #   - MAC globale;
            #   - permanenza lunga sul BSSID;
            #   - almeno 12 NULL frame TX distribuiti nel tempo;
            #   - quasi solo frame piccoli;
            # è sufficiente per mantenerla come POSSIBILE camera idle.
            #
            # La regola è volutamente limitata a Trolink per non trasformare
            # normali telefoni/PC in falsi positivi.
            trolink_null_keepalive_exception = bool(
                identity == 8
                and "trolink" in vlow
                and not locally_administered
                and duration >= 60
                and capture_duration >= 60
                and _trolink_span_ratio >= 0.60
                and st["null_frames"] >= 12
                and st["null_tx_frames"] >= 12
                and st["tx_frames"] >= 12
                and small_ratio >= 0.95
                and retry_ratio < 0.25
            )

            low_traffic_wifi_camera = bool(
                low_traffic_wifi_camera
                or persistent_embedded_idle
                or sparse_embedded_idle
                or embedded_camera_exception
                or trolink_null_keepalive_exception
            )
            if low_traffic_wifi_camera:
                # Il comportamento non dimostra da solo che sia una camera, ma con
                # vendor embedded/camera + persistenza quasi continua merita almeno
                # la classe POSSIBILE.
                score = max(
                    score,
                    48 if embedded_camera_exception else
                    47 if trolink_null_keepalive_exception else
                    46 if persistent_embedded_idle else
                    45 if sparse_embedded_idle else
                    44
                )
                if trolink_null_keepalive_exception:
                    reasons.append(
                        f"Trolink idle NULL keepalive signature ({st['null_frames']} NULL frames)"
                        if is_en else
                        f"firma Trolink idle con keepalive NULL ({st['null_frames']} frame NULL)"
                    )
                elif embedded_camera_exception:
                    reasons.append(
                        "persistent Trolink Wi-Fi camera/embedded idle signature"
                        if is_en else
                        "firma Trolink Wi-Fi embedded/camera idle persistente"
                    )
                elif sparse_embedded_idle:
                    reasons.append(
                        "sparse idle embedded Wi-Fi camera signature"
                        if is_en else
                        "firma telecamera Wi-Fi embedded idle a intervalli"
                    )
                else:
                    reasons.append(
                        "persistent idle embedded Wi-Fi camera signature"
                        if (is_en and persistent_embedded_idle) else
                        "persistent low-traffic embedded Wi-Fi camera signature"
                        if is_en else
                        "firma telecamera Wi-Fi embedded idle persistente"
                        if persistent_embedded_idle else
                        "firma telecamera Wi-Fi embedded a basso traffico"
                    )

            # MAC localmente amministrato: ammesso solo con evidenza molto forte.
            # Questo sostituisce la vecchia esclusione assoluta.
            if locally_administered and identity < 20:
                random_mac_strong = bool(
                    duration >= 60
                    and st["useful_frames"] >= 250
                    and activity_ratio >= 0.65
                    and tx_activity >= 0.55
                    and tx_ratio >= 0.78
                    and temporal >= 3
                )
                if not random_mac_strong:
                    continue
                reasons.append(
                    "locally administered MAC but strong persistent camera-like behavior"
                    if is_en else
                    "MAC locale ma comportamento persistente fortemente compatibile"
                )

            # Filtro generale: la tabella telecamere NON deve contenere ogni client.
            # I vendor generici devono mostrare una vera impronta video/cloud; i
            # vendor misti possono entrare a bassa confidenza con una firma moderata.
            wifi_video_signals = 0
            if tx_ratio >= 0.82 and direction >= 17:
                wifi_video_signals += 1
            if duration >= 45 and activity_ratio >= 0.55 and continuity >= 7:
                wifi_video_signals += 1
            if st["useful_frames"] >= 180 and large_ratio >= 0.40 and shape >= 7:
                wifi_video_signals += 1
            if tx_activity >= 0.50 and p95_tx_rate >= 0.35 and tx_rate_cv < 1.15:
                wifi_video_signals += 1
            if temporal >= 3 and len(gaps) >= 20:
                wifi_video_signals += 1

            if identity >= 20 and not low_traffic_wifi_camera and not cloud_stream_strong:
                # Anche un OUI CCTV puo' appartenere a recorder/citofoni/controller.
                # Se il traffico e' debole lo mostriamo solo quando c'e' una presenza
                # reale e persistente, e soltanto come DA OSSERVARE.
                vendor_weak_but_present = bool(
                    duration >= 20 and st["useful_frames"] >= 20
                    and (continuity >= 7 or direction >= 9 or temporal >= 3)
                )
                if not vendor_weak_but_present:
                    continue
                score = max(36, min(score, 41))
                reasons.append(
                    "camera vendor but no confirmed streaming: observation only"
                    if is_en else "vendor camera ma streaming non confermato: solo da osservare"
                )

            elif identity == 10 and not low_traffic_wifi_camera:
                mixed_mid = bool(
                    wifi_video_signals >= 2
                    or (cloud_stream_strong and wifi_video_signals >= 1)
                    or (duration >= 35 and st["useful_frames"] >= 100
                        and tx_ratio >= 0.65 and activity_ratio >= 0.40
                        and (shape >= 7 or continuity >= 13))
                )
                if not mixed_mid:
                    continue
                if wifi_video_signals < 2 and score < 42:
                    score = max(36, score)

            elif identity < 10 and not low_traffic_wifi_camera:
                # Vendor generico/ignoto: servono almeno DUE segnali indipendenti
                # e un uplink realmente persistente. Con 3+ segnali e' POSSIBILE;
                # con 2 resta DA OSSERVARE.
                generic_mid = bool(
                    wifi_video_signals >= 2
                    and duration >= 35
                    and st["useful_frames"] >= 100
                    and tx_ratio >= 0.70
                    and activity_ratio >= 0.40
                    and (cloud_stream_strong or direction >= 17)
                )
                if not generic_mid:
                    continue
                if wifi_video_signals == 2:
                    score = max(36, min(score, 41))
                    reasons.append(
                        "moderate generic camera/video fingerprint 2/5"
                        if is_en else "impronta camera/video generica moderata 2/5"
                    )
                else:
                    reasons.append(
                        f"generic camera/video fingerprint {wifi_video_signals}/5"
                        if is_en else f"impronta camera/video generica {wifi_video_signals}/5"
                    )

            # Via di mezzo: la fascia DA OSSERVARE esiste, ma parte da 36/100 e
            # solo dopo avere superato i filtri comportamentali sopra.
            if score < 36:
                continue
            if score >= 80: level=("HIGHLY LIKELY" if is_en else "MOLTO PROBABILE")
            elif score >= 62: level=("LIKELY" if is_en else "PROBABILE")
            elif score >= 42: level=("POSSIBLE" if is_en else "POSSIBILE")
            else: level=("LOW CONFIDENCE" if is_en else "DA OSSERVARE")

            txrx=f"{tx/1048576:.1f}/{rx/1048576:.1f} MB"
            bit=f"{bitrate:.2f} Mbps"
            dur=f"{duration:.0f} s"
            conf=int(round(confidence*100))

            # Deduplica motivazioni mantenendo l'ordine e mostra le piu' significative.
            unique=[]
            for r in reasons:
                if r and r not in unique:
                    unique.append(r)
            indicators=("; ".join(unique[:8]) or
                        ("compatible IEEE 802.11 traffic metadata" if is_en else "metadati 802.11 compatibili")) + f"; conf {conf}%"
            self.camera_candidate_details[mac]={
                "mac":mac,"vendor":vendor,"score":score,"level":level,"confidence":conf,
                "provenance":"WIFI",
                "class":classes.get(mac,("UNDETERMINED" if is_en else "NON DETERMINATA")),"frames":st["frames"],
                "null_frames":st["null_frames"],"null_tx_frames":st["null_tx_frames"],
                "tx_frames":st["tx_frames"],"rx_frames":st["rx_frames"],"tx_bytes":tx,"rx_bytes":rx,
                "duration":duration,"bitrate":bitrate,"tx_bitrate":tx_bitrate,"tx_ratio":tx_ratio,
                "activity_ratio":activity_ratio,"tx_activity":tx_activity,
                "presence":presence_ratio_capture,"presence_ratio":presence_ratio_capture,
                "continuity":activity_ratio,"continuity_score":continuity,
                "regularity":(0.0 if tx_rate_cv>=90 else max(0.0,1.0-min(1.0,tx_rate_cv))),
                "avg_len":mean(st["useful_lengths"] or st["lengths"]),
                "avg_frame_size":mean(st["useful_lengths"] or st["lengths"]),
                "large_ratio":large_ratio,"small_ratio":small_ratio,"retry_ratio":retry_ratio,
                "gap_mean":gap_mean,"mean_iat":gap_mean,"inter_arrival":gap_mean,"gap_cv":gap_cv,"p95_rate":p95_rate,"p95_tx_rate":p95_tx_rate,
                "burst_cv":burst_cv,"tx_rate_cv":tx_rate_cv,"mean_signal":mean(st["signals"]) if st["signals"] else 0.0,
                "avg_signal":mean(st["signals"]) if st["signals"] else 0.0,
                "reasons":unique,
                "traffic_profile": (
                    "CAMERA CLOUD STREAMING" if cloud_stream_very_strong else
                    "CAMERA CLOUD COMPATIBLE" if cloud_stream_strong else
                    "CAMERA IDLE/CLOUD KEEPALIVE" if low_traffic_wifi_camera else
                    "CAMERA-LIKE TRAFFIC"
                ),
                "brand_assessment":vendor if identity>=20 else ("NOT DETERMINABLE FROM TRAFFIC ALONE" if is_en else "NON DETERMINABILE DAL SOLO TRAFFICO"),
                "score_parts":{"identita":identity,"protocollo":0,"direzione":direction,"continuita":continuity,
                    "forma":shape,"temporale":temporal,"radio":radio,"presenza":presence,
                    "penalita":penalty,"incertezza":uncertainty_penalty}
            }
            out.append((mac,vendor,f"{score}/100",level,txrx,"WIFI",dur,indicators))

        # Estensione LAN: usa gli endpoint DS/LAN osservati nello stesso PCAP e,
        # con prudenza, dispositivi camera-oriented scoperti dalla LAN attiva.
        try:
            lan_rows = self._analyze_lan_camera_candidates(cap, bssid)
        except Exception as e:
            self.logmsg(
                ("LAN camera analysis error: " if is_en else "Errore analisi telecamere LAN: ")
                + str(e)
            )
            lan_rows = []

        # Algoritmo separato: possibili telecamere dietro router NAT in cascata.
        try:
            cascade_rows = self._analyze_cascade_router_camera_candidates(cap, bssid)
        except Exception as e:
            self.logmsg(("Cascade-router camera analysis error: " if is_en else
                         "Errore analisi camera dietro router cascata: ") + str(e))
            cascade_rows = []

        # Algoritmo DVR/NVR SEPARATO: usa i risultati LAN disponibili ma
        # non cambia nessuna soglia/formula del motore telecamere.
        try:
            dvr_rows = self._analyze_dvr_nvr_candidates_separate(lan_rows, observed_rows, cap, bssid)
        except Exception as e:
            self.logmsg(
                ("NVR analysis error: " if is_en else "Errore analisi NVR: ") + str(e)
            )
            dvr_rows = []

        # Un MAC visto direttamente come station Wi-Fi prevale sempre come WIFI.
        # In caso contrario, conserva la variante con score più alto.
        merged = {}
        for row in list(out) + list(lan_rows) + list(cascade_rows) + list(dvr_rows):
            mac_r = str(row[0]).lower()
            old = merged.get(mac_r)
            if old is None:
                merged[mac_r] = row
                continue
            try:
                old_score = int(str(old[2]).split("/")[0])
                new_score = int(str(row[2]).split("/")[0])
            except Exception:
                old_score = new_score = 0
            if str(old[5]).upper() == "WIFI":
                continue
            if str(row[5]).upper() == "WIFI" or new_score > old_score:
                merged[mac_r] = row

        return sorted(merged.values(), key=lambda r:(-int(r[2].split('/')[0]), r[0]))


    def _start_async_live_mac_check(self, cap, bssid, client):
        """Analizza periodicamente uno snapshot del PCAP senza bloccare la barra."""
        if self.live_mac_check_running:
            return
        if not cap or not Path(cap).exists():
            return

        self.live_mac_check_running = True

        # L'analisi telecamere e' piu' costosa della sola panoramica MAC.
        # Durante la cattura la eseguiamo al massimo ogni 6 secondi; a fine
        # cattura viene comunque eseguita sempre sull'intero PCAP definitivo.
        now_camera = time.monotonic()
        next_camera = float(getattr(self, "_camera_live_next_at", 0.0) or 0.0)
        do_camera_analysis = now_camera >= next_camera
        if do_camera_analysis:
            self._camera_live_next_at = now_camera + 6.0

        def worker():
            snapshot = None
            try:
                src = Path(cap)
                snapshot = src.with_name(src.stem + ".mac_snapshot" + src.suffix)

                try:
                    shutil.copyfile(src, snapshot)
                    target = snapshot
                except Exception:
                    target = src

                rows = self.analyze(target, bssid, client)
                self.root.after(
                    0,
                    lambda data=rows: self._merge_live_mac_rows(data)
                )

                if do_camera_analysis:
                    camera_rows = self.analyze_camera_candidates(target, bssid, rows)
                    if getattr(self, "_cascade_second_scan_running", False):
                        self.root.after(
                            0,
                            lambda data=camera_rows: self._cascade_realtime_camera_association(data)
                        )
                    else:
                        self.root.after(
                            0,
                            lambda data=camera_rows: self._merge_camera_candidate_rows(data)
                        )
            except Exception as e:
                self.logmsg(f"Analisi MAC live: {e}")
            finally:
                if snapshot is not None:
                    try:
                        snapshot.unlink(missing_ok=True)
                    except Exception:
                        pass
                self.live_mac_check_running = False

        threading.Thread(target=worker, daemon=True).start()

    def _capture_worker(self,iface,bssid,ch,client,duration,repetitions,pause_seconds,capture_kind="manual",run_id=None):
        try:
            if run_id is None:
                run_id = getattr(self, "capture_run_id", 0)

            # Per la cattura manuale il 100% viene mostrato SOLO dopo che
            # airodump-ng ha chiuso il PCAP finale e _archive_capture()/copy2
            # ha terminato realmente la creazione del file definitivo.
            manual_final_file_ready = False

            def session_current():
                return run_id == getattr(self, "capture_run_id", 0)

            def safe_progress(percent, text=None, phase=None, detail=None):
                if session_current():
                    p = float(percent)
                    if capture_kind == "manual" and not manual_final_file_ready and p >= 100.0:
                        p = 99.0
                        if text is None or str(text).strip() in ("100", "100%"):
                            text = "99%"
                    self.set_progress(p, text, phase, detail)

            def safe_status(message):
                if session_current():
                    self.set_status(message)

            if not session_current():
                return

            run(["iw","dev",iface,"set","channel",ch], timeout=5)

            if not session_current():
                return

            aggregate={}

            duration=max(1,int(duration))
            repetitions=max(1,int(repetitions))
            pause_seconds=max(0,int(pause_seconds))

            total_capture=float(duration*repetitions)
            total_pause=float(pause_seconds*max(0,repetitions-1))
            total_work=max(1.0,total_capture+total_pause)
            elapsed_work=0.0

            self.logmsg(
                f"Parametri cattura: durata={duration}s, ripetizioni={repetitions}, "
                f"attesa={pause_seconds}s"
            )

            stopped_by_handshake=False
            handshake_pcap_archived=False
            for cycle in range(1,repetitions+1):
                if not session_current():
                    break
                if self.capture_stop.is_set():
                    stopped_by_handshake = (
                        capture_kind == "handshake"
                        and self.handshake_latched
                        and self.stop_on_handshake_event.is_set()
                    )
                    break
                stamp=datetime.now().strftime("%Y%m%d_%H%M%S_%f")
                prefix=self.outdir/f"capture_{stamp}_r{cycle}"
                cap=Path(str(prefix)+"-01.cap")

                cmd=[
                    "airodump-ng",
                    "--bssid",bssid,
                    "--channel",ch,
                    "--write",str(prefix),
                    "--output-format","pcap",
                    iface
                ]

                self.logmsg("$ "+" ".join(cmd))
                safe_status(f"Cattura {cycle}/{repetitions} in corso...")

                proc=popen_logged(
                    cmd,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    text=True
                )
                if not session_current():
                    try:
                        proc.terminate()
                    except Exception:
                        pass
                    return
                self.capture_process = proc

                # Solo la CATTURA PASSIVA manuale conta come azione "passive".
                # La cattura parallela della modalità attiva/handshake non deve
                # bloccare una futura proposta di scansione passiva dedicata.
                if capture_kind == "manual":
                    self._dual_band_mark_action_scanned("passive", bssid, ch)

                cycle_start=time.monotonic()
                next_hs_check=cycle_start+2.0
                stopped_for_handshake=False

                while True:
                    if not session_current():
                        break
                    now=time.monotonic()
                    cycle_elapsed=min(float(duration),now-cycle_start)
                    remaining=max(0,int(round(duration-cycle_elapsed)))

                    overall=((elapsed_work+cycle_elapsed)/total_work)*100.0
                    safe_progress(
                        overall,
                        f"{overall:.0f}%",
                        "CATTURA",
                        f"Cattura {cycle}/{repetitions} - {remaining}s rimanenti"
                    )

                    if cap.exists() and now >= next_hs_check:
                        # Controllo handshake SEMPRE attivo: sia CATTURA PASSIVA
                        # sia DISTURBO. Non richiede la password Wi-Fi perché EAPOL
                        # e header 802.11 necessari alla verifica restano osservabili.
                        self._start_async_handshake_check(
                            cap, bssid,
                            stop_on_found=(capture_kind == "handshake")
                        )
                        self._start_async_live_mac_check(cap,bssid,client)
                        next_hs_check=now+2.0

                    if self.capture_stop.is_set():
                        # Arresto manuale/esterno: vale per entrambe le modalità.
                        break

                    if (
                        capture_kind == "handshake"
                        and self.handshake_found_async
                        and self.stop_on_handshake_event.is_set()
                    ):
                        stopped_for_handshake=True
                        stopped_by_handshake=True
                        self.capture_stop.set()
                        self.logmsg(
                            "Handshake completo rilevato durante DISTURBO: arresto cattura PCAP richiesto."
                        )
                        break

                    if cycle_elapsed >= duration:
                        break

                    # Se airodump termina prima del tempo previsto, non lasciare
                    # il worker bloccato: esci e registra l'evento.
                    if proc.poll() is not None:
                        self.logmsg(
                            f"airodump-ng terminato prima del previsto nella cattura "
                            f"{cycle}/{repetitions} (exit={proc.returncode})."
                        )
                        break

                    time.sleep(0.05)

                # Termina airodump al termine della finestra.
                if proc.poll() is None:
                    proc.terminate()
                    try:
                        proc.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        try:
                            proc.wait(timeout=2)
                        except subprocess.TimeoutExpired:
                            pass
                if self.capture_process is proc:
                    self.capture_process = None

                actual_elapsed=min(float(duration),time.monotonic()-cycle_start)

                # Anche se il processo termina poco prima, ai fini della sequenza
                # temporale consideriamo completata la finestra trascorsa davvero.
                elapsed_work += actual_elapsed
                overall=min(100.0,(elapsed_work/total_work)*100.0)
                if self.capture_stop.is_set() and not stopped_by_handshake:
                    # Arresto manuale (FERMA CATTURA / FERMA DISTURBO):
                    # la barra deve restare a zero e non essere riscritta dal worker.
                    safe_progress(
                        0,
                        "0%",
                        "PRONTO",
                        "Cattura arrestata manualmente"
                    )
                elif stopped_for_handshake:
                    safe_progress(
                        overall,
                        f"{overall:.0f}%",
                        "ARRESTATO",
                        "Handshake completo trovato - cattura fermata"
                    )
                else:
                    safe_progress(
                        overall,
                        f"{overall:.0f}%",
                        "ANALISI",
                        f"Analisi cattura {cycle}/{repetitions}"
                    )

                if cap.exists():
                    self.capture_file=cap

                    try:
                        self.check_handshake(
                            cap, bssid,
                            stop_on_found=(capture_kind == "handshake")
                        )
                    except Exception as e:
                        self.logmsg(f"Controllo handshake finale: {e}")

                    # Archivia il PCAP definitivo nella cartella CATTURE.
                    # La cattura manuale viene sempre archiviata come CATTURA_*.
                    # La cattura parallela a DIEGO viene archiviata una sola volta,
                    # esclusivamente quando il 4-way handshake è stato trovato.
                    if capture_kind == "manual":
                        archived_capture = self._archive_capture(cap, "manual")
                        if (
                            archived_capture is not None
                            and cycle == repetitions
                            and session_current()
                            and not self.capture_stop.is_set()
                        ):
                            manual_final_file_ready = True
                            safe_progress(
                                100,
                                "100%",
                                "COMPLETED" if getattr(self,"language","it")=="en" else "COMPLETATO",
                                (
                                    "Final PCAP file created"
                                    if getattr(self,"language","it")=="en"
                                    else "File PCAP definitivo creato"
                                )
                            )
                    elif (
                        capture_kind == "handshake"
                        and self.handshake_latched
                        and not handshake_pcap_archived
                    ):
                        if self._archive_capture(cap, "handshake") is not None:
                            handshake_pcap_archived=True

                    try:
                        rows=self.analyze(cap,bssid,client)
                        camera_rows=self.analyze_camera_candidates(cap,bssid,rows)

                        if getattr(self, "_cascade_second_scan_running", False):
                            try:
                                self.root.after(
                                    0,
                                    lambda data=camera_rows: self._cascade_realtime_camera_association(data)
                                )
                                self._cascade_second_scan_collect_links(camera_rows)
                            except Exception:
                                pass

                        # Algoritmo separato di collegamento per la seconda scansione.
                        # Vale sia per una camera LAN sia per una camera Wi-Fi trovata
                        # sul secondo BSSID, senza modificare i motori di rilevamento.
                        if getattr(self, "_cascade_second_scan_running", False):
                            try:
                                _ph = set(getattr(self, "_cascade_router_cam_placeholders", set()) or set())
                                for _r in (camera_rows or []):
                                    if not _r:
                                        continue
                                    _m = str(_r[0] if len(_r) > 0 else "").lower()
                                    if not MAC_FULL.match(_m) or _m in _ph:
                                        continue
                                    _d = self.camera_candidate_details.setdefault(_m, {})
                                    if _d.get("nvr_candidate") or _d.get("cascade_camera_candidate"):
                                        continue
                                    _d["router_cam_confirmed"] = True
                                    _d["cascade_parent_bssid"] = getattr(
                                        self, "_cascade_second_scan_target_bssid", ""
                                    )
                            except Exception:
                                pass

                        if getattr(self, "_cascade_second_scan_running", False):
                            try:
                                _dbg = " | ".join(
                                    f"{r[0]}:{r[5]}:{r[2]}:{r[3]}"
                                    for r in (camera_rows or [])
                                    if len(r) >= 6
                                )
                                self.logmsg(
                                    "SECONDA SCANSIONE ROUTER-CAM - candidati finali: "
                                    + (_dbg or "NESSUNO")
                                )
                            except Exception:
                                pass

                        if (capture_kind == "manual" and cycle == repetitions
                                and getattr(self, "_cascade_second_scan_running", False)):
                            # SECONDA scansione: il merge finale è quello che
                            # sostituisce CAM DIETRO ROUTER con ROUTER-CAM.
                            self.root.after(
                                0,
                                lambda data=camera_rows:
                                    self._merge_camera_candidate_rows_cascade_final(data)
                            )

                        else:
                            self.root.after(
                                0,
                                lambda data=camera_rows:
                                    self._merge_camera_candidate_rows(data)
                            )

                        if capture_kind == "manual" and cycle == repetitions:
                            self.root.after(
                                900,
                                lambda c=cap, data=list(rows), bb=bssid, cc=ch, rr=run_id:
                                    self._passive_post_scan_workflow(
                                        c, data, bb, cc, rr
                                    )
                            )

                    except Exception as e:
                        self.logmsg(f"Analisi MAC fallita: {e}")
                        rows=[]

                    assoc_clients=self.clients_from_analysis_rows(rows)
                    selected_band=self.band_from_channel(ch)
                    self.root.after(
                        0,
                        self.update_ap_client_count_display,
                        bssid,
                        len(assoc_clients),
                        selected_band
                    )

                    for row in rows:
                        if len(row)<5:
                            continue
                        mac,vendor,cls,evidence,notes=row[:5]
                        rec=aggregate.setdefault(
                            mac,[vendor,set(),set(),set()]
                        )
                        rec[1].add(cls)
                        if evidence:
                            rec[2].add(evidence)
                        if notes:
                            rec[3].add(notes)

                    merged=[]
                    for mac in sorted(aggregate):
                        vendor,classes,evidence_set,notes_set=aggregate[mac]
                        cls=self.best_class(classes)
                        merged.append((
                            mac,
                            vendor,
                            cls,
                            " | ".join(sorted(evidence_set)),
                            " | ".join(sorted(notes_set))
                        ))

                    self.root.after(
                        0,
                        lambda data=merged:self._merge_live_mac_rows(data, replace=True)
                    )
                else:
                    self.logmsg(
                        f"Cattura {cycle}/{repetitions}: file PCAP non creato."
                    )

                if stopped_for_handshake:
                    break

                # Attesa reale tra una ripetizione e la successiva.
                if cycle < repetitions and pause_seconds > 0:
                    pause_start=time.monotonic()

                    while True:
                        if self.capture_stop.is_set():
                            stopped_by_handshake = (
                                capture_kind == "handshake"
                                and self.handshake_latched
                                and self.stop_on_handshake_event.is_set()
                            )
                            break
                        pause_elapsed=min(
                            float(pause_seconds),
                            time.monotonic()-pause_start
                        )
                        if pause_elapsed >= pause_seconds:
                            break

                        left=max(0,int(round(pause_seconds-pause_elapsed)))
                        overall=(
                            (elapsed_work+pause_elapsed)/total_work
                        )*100.0
                        safe_progress(
                            overall,
                            f"{overall:.0f}%",
                            "ATTESA",
                            f"Attesa {left}s prima della cattura "
                            f"{cycle+1}/{repetitions}"
                        )
                        time.sleep(0.05)

                    if self.capture_stop.is_set():
                        break

                    elapsed_work += pause_seconds

                    overall=min(
                        100.0,
                        (elapsed_work/total_work)*100.0
                    )
                    safe_progress(
                        overall,
                        f"{overall:.0f}%",
                        "PREPARAZIONE",
                        f"Avvio cattura {cycle+1}/{repetitions}"
                    )

            # Porta al 100% SOLO se questa è ancora la sessione corrente
            # e la cattura è terminata naturalmente.
            natural_completion = (
                session_current()
                and not stopped_by_handshake
                and not self.capture_stop.is_set()
                and elapsed_work >= (total_capture - 0.25)
                and (capture_kind != "manual" or manual_final_file_ready)
            )
            if natural_completion:
                safe_progress(
                    100,
                    "100%",
                    "COMPLETED" if getattr(self,"language","it")=="en" else "COMPLETATO",
                    (
                        f"Completed {repetitions} capture(s)"
                        if getattr(self,"language","it")=="en"
                        else f"Completate {repetitions} ripetizioni"
                    )
                )
                if capture_kind == "handshake":
                    self.root.after(20, self._finish_disturb_ui_when_complete)

            final_rows=[]
            for mac in sorted(aggregate):
                vendor,classes,evidence_set,notes_set=aggregate[mac]
                cls=self.best_class(classes)
                final_rows.append((
                    mac,
                    vendor,
                    cls,
                    " | ".join(sorted(evidence_set)),
                    " | ".join(sorted(notes_set))
                ))

            if final_rows and session_current():
                self.root.after(
                    0,
                    lambda data=final_rows:self._merge_live_mac_rows(data, replace=True)
                )

            if session_current():
                if stopped_by_handshake:
                    safe_status(
                        "Handshake found: PCAP capture stopped."
                        if getattr(self,"language","it")=="en"
                        else "Handshake trovato: cattura PCAP arrestata."
                    )
                elif natural_completion:
                    safe_status(
                        "Capture completed."
                        if getattr(self,"language","it")=="en"
                        else "Cattura completata."
                    )

            # Per la cattura manuale il relativo comando è terminato:
            # a tempo scaduto + barra 100% la sessione è considerata FINITA,
            # equivalente allo stato ottenuto dopo FERMA, ma senza azzerare la barra.
            if capture_kind == "manual" and session_current():
                self.capture_process = None

                if natural_completion:
                    # Fine naturale: 100% e sessione conclusa.
                    self.capture_stop.set()
                    safe_progress(
                        100,
                        "100%",
                        "COMPLETED" if getattr(self,"language","it")=="en" else "COMPLETATO",
                        (
                            "Capture duration completed"
                            if getattr(self,"language","it")=="en"
                            else "Tempo impostato terminato - cattura conclusa"
                        )
                    )
                    safe_status(
                        "Capture completed."
                        if getattr(self,"language","it")=="en"
                        else "Cattura terminata."
                    )
                    try:
                        self._schedule_dual_band_warning_check(bssid,ch)
                    except Exception:
                        pass
                else:
                    # STOP manuale: resta a 0%. Un successivo AVVIA parte da zero
                    # con timer, worker e barra completamente nuovi.
                    safe_progress(
                        0,
                        "0%",
                        "READY" if getattr(self,"language","it")=="en" else "PRONTO",
                        (
                            "Capture stopped - ready for a new session"
                            if getattr(self,"language","it")=="en"
                            else "Cattura arrestata - pronta per una nuova sessione"
                        )
                    )

                self._set_export_button_enabled("capture", True)
                self._stop_button_blink("start_capture_button")
                self._stop_passive_mode_banner_blink()
                self._manual_capture_banner_active = False
                self._set_operation_mode_banner("idle")
                self._release_suspend_inhibitor_later("capture")

        except Exception as e:
            self.logmsg(f"ERRORE _capture_worker: {type(e).__name__}: {e}")
            if session_current():
                safe_status(
                    f"Capture error: {e}"
                    if getattr(self,"language","it")=="en"
                    else f"Errore cattura: {e}"
                )
            if capture_kind == "manual" and session_current():
                self._set_export_button_enabled("capture", True)
                self._stop_button_blink("start_capture_button")
                self._stop_passive_mode_banner_blink()
                self._manual_capture_banner_active = False
                self._set_operation_mode_banner("idle")
                self._release_suspend_inhibitor_later("capture")


    @staticmethod
    def is_multicast_or_broadcast(mac):
        try:
            first = int(mac.split(":")[0], 16)
            return mac == "ff:ff:ff:ff:ff:ff" or bool(first & 0x01)
        except Exception:
            return False

    @staticmethod
    def best_class(classes):
        # Priorità: l'osservazione più specifica prevale sulle categorie incerte.
        priority = {
            "AP": 5,
            "Wi-Fi ASSOCIATO": 4,
            "LAN CANDIDATO": 3,
            "MULTICAST/BROADCAST": 2,
            "ALTRO/INCERTO": 1,
        }
        return max(classes, key=lambda c: priority.get(c, 0)) if classes else "ALTRO/INCERTO"

    def check_handshake(self, cap, bssid, stop_on_found=False):
        """Analizza passivamente EAPOL/4-way handshake nel PCAP."""
        if not cap or not Path(cap).exists():
            return False

        bssid=(bssid or "").strip().lower()
        if not MAC_FULL.match(bssid):
            self.logmsg("Handshake: BSSID non valido")
            return False

        def first_value(value):
            return (value or "").split(",", 1)[0].strip()

        def as_int(value):
            value=first_value(value).lower()
            if not value:
                return None
            try:
                return int(value, 0)
            except ValueError:
                try:
                    return int(value, 16)
                except ValueError:
                    return None

        def as_flag(value):
            text=first_value(value).lower()
            if text in {"true","yes","set"}:
                return True
            if text in {"false","no","not set"}:
                return False
            number=as_int(value)
            return None if number is None else bool(number)

        # Catalogo campi TShark. Se non è disponibile, lavoriamo con un profilo
        # minimo invece di mostrare in GUI gli errori interni del dissector.
        if self._tshark_fields_cache is None:
            catalog=run(["tshark","-G","fields"], timeout=10)
            available=set()
            if catalog.returncode == 0:
                for line in catalog.stdout.splitlines():
                    cols=line.split("\t")
                    if len(cols) > 2 and cols[0] == "F":
                        available.add(cols[2].strip())
            self._tshark_fields_cache=available

        available=self._tshark_fields_cache or set()

        # Campi sempre molto comuni; i profili successivi eliminano TA/RA se la
        # build TShark non li accetta.
        address_profiles=[
            ["frame.time_epoch","frame.number","wlan.sa","wlan.da","wlan.ta","wlan.ra","wlan.bssid"],
            ["frame.time_epoch","frame.number","wlan.sa","wlan.da","wlan.bssid"],
            ["frame.time_epoch","frame.number","wlan.sa","wlan.da"],
        ]

        optional_candidates=[
            "wlan_rsna_eapol.keydes.msgnr",
            "eapol.keydes.msgnr",
            "wlan_rsna_eapol.keydes.key_info",
            "wlan_rsna_eapol.keydes.key_info.key_ack",
            "wlan_rsna_eapol.keydes.key_info.key_mic",
            "wlan_rsna_eapol.keydes.key_info.install",
            "wlan_rsna_eapol.keydes.key_info.secure",
            "wlan_rsna_eapol.keydes.key_info.request",
            "wlan_rsna_eapol.keydes.key_info.error",
            "wlan_rsna_eapol.keydes.key_info.key_type",
            "wlan_rsna_eapol.keydes.replay_counter",
            "wlan_rsna_eapol.keydes.nonce",
            "wlan_rsna_eapol.keydes.data_len",
        ]
        if available:
            optional=[x for x in optional_candidates if x in available]
        else:
            # Se il catalogo non è leggibile, non rischiare un comando pieno di
            # campi sconosciuti: il profilo minimo rileva comunque gli EAPOL.
            optional=[]

        msg_fields=[x for x in (
            "wlan_rsna_eapol.keydes.msgnr",
            "eapol.keydes.msgnr",
            "wlan_rsna_eapol.keydes.replay_counter",
            "wlan_rsna_eapol.keydes.nonce",
        ) if x in optional]
        bit_fields=[x for x in (
            "wlan_rsna_eapol.keydes.key_info",
            "wlan_rsna_eapol.keydes.key_info.key_ack",
            "wlan_rsna_eapol.keydes.key_info.key_mic",
            "wlan_rsna_eapol.keydes.key_info.install",
            "wlan_rsna_eapol.keydes.key_info.secure",
            "wlan_rsna_eapol.keydes.key_info.request",
            "wlan_rsna_eapol.keydes.key_info.error",
            "wlan_rsna_eapol.keydes.key_info.key_type",
            "wlan_rsna_eapol.keydes.replay_counter",
            "wlan_rsna_eapol.keydes.nonce",
            "wlan_rsna_eapol.keydes.data_len",
        ) if x in optional]

        optional_profiles=[]
        for profile in (optional, msg_fields, bit_fields, []):
            profile=list(dict.fromkeys(profile))
            if profile not in optional_profiles:
                optional_profiles.append(profile)

        # Prima usa il filtro generico eapol. Alcune build accettano il filtro
        # eapol.type==3 ma restituiscono zero righe in catture dove il dissector
        # non valorizza eapol.type come previsto.
        successful=[]
        extraction_errors=[]
        for display_filter in ("eapol", "eapol.type == 3"):
            for base_fields in address_profiles:
                # Se conosciamo il catalogo, salta subito i profili con campi base assenti.
                if available and any(x not in available for x in base_fields):
                    continue
                for opt in optional_profiles:
                    trial_fields=base_fields+opt
                    cmd=[
                        "tshark","-r",str(cap),"-Y",display_filter,
                        "-T","fields","-E","separator=/t","-E","occurrence=f"
                    ]
                    for name in trial_fields:
                        cmd.extend(["-e",name])
                    trial=run(cmd, timeout=10)
                    # Su un PCAP copiato mentre la cattura è attiva TShark può
                    # segnalare "cut short" sull'ultimo pacchetto e uscire con
                    # codice 2, ma stdout contiene comunque frame EAPOL validi.
                    # In quel caso NON scartiamo i risultati già estratti.
                    usable = (trial.returncode == 0) or bool((trial.stdout or "").strip())
                    if usable:
                        successful.append((len(trial.stdout.splitlines()), trial, trial_fields, display_filter))
                        if trial.returncode != 0:
                            warn=" ".join((trial.stderr or "").split())[:220]
                            if warn:
                                self.logmsg("TShark ha letto dati EAPOL con avviso: " + warn)
                        # Se abbiamo già dati reali, questo profilo è sufficiente.
                        if trial.stdout.strip():
                            break
                    else:
                        err=" ".join((trial.stderr or "").split())[:260]
                        if err:
                            extraction_errors.append(err)
                if successful and successful[-1][0] > 0:
                    break
            if successful and successful[-1][0] > 0:
                break

        if not successful:
            detail="TShark non riesce a leggere i campi EAPOL di questa cattura"
            self.logmsg(detail)
            if extraction_errors:
                self.logmsg("Dettaglio TShark: " + extraction_errors[-1])
            # Errore tecnico solo nel log: il riquadro resta pulito e leggibile.
            # Durante una cattura il file può essere temporaneamente non leggibile.
            return False

        # Preferisci il profilo con più righe; a parità quello con più campi.
        successful.sort(key=lambda x:(x[0], len(x[2])), reverse=True)
        _,p,fields,used_filter=successful[0]
        self.logmsg(f"Analisi EAPOL: filtro={used_filter}, campi={len(fields)}")

        frames_by_sta={}
        raw_eapol_lines=0
        accepted_eapol=0
        discarded_no_ap=0
        discarded_no_sta=0

        for line in p.stdout.splitlines():
            if not line.strip():
                continue
            raw_eapol_lines += 1
            values=line.split("\t")
            values += [""]*(len(fields)-len(values))
            row=dict(zip(fields, values))
            sa=first_value(row.get("wlan.sa")).lower()
            da=first_value(row.get("wlan.da")).lower()
            ta=first_value(row.get("wlan.ta")).lower()
            ra=first_value(row.get("wlan.ra")).lower()
            fb=first_value(row.get("wlan.bssid")).lower()

            valid_addrs=[x for x in (sa,da,ta,ra,fb) if MAC_FULL.match(x)]
            if bssid not in valid_addrs:
                discarded_no_ap += 1
                continue

            sta=""
            direction=""
            if ta == bssid and MAC_FULL.match(ra) and ra != bssid:
                sta,direction=ra,"ap_to_sta"
            elif ra == bssid and MAC_FULL.match(ta) and ta != bssid:
                sta,direction=ta,"sta_to_ap"
            elif sa == bssid and MAC_FULL.match(da) and da != bssid:
                sta,direction=da,"ap_to_sta"
            elif da == bssid and MAC_FULL.match(sa) and sa != bssid:
                sta,direction=sa,"sta_to_ap"
            else:
                candidates_sta=[]
                for cand in (ta,ra,sa,da):
                    if (MAC_FULL.match(cand) and cand != bssid and
                            not self.is_multicast_or_broadcast(cand) and
                            cand not in candidates_sta):
                        candidates_sta.append(cand)
                if len(candidates_sta) == 1:
                    sta=candidates_sta[0]
                    if bssid in (ta,sa):
                        direction="ap_to_sta"
                    elif bssid in (ra,da):
                        direction="sta_to_ap"

            if not sta or not MAC_FULL.match(sta) or self.is_multicast_or_broadcast(sta):
                discarded_no_sta += 1
                continue
            accepted_eapol += 1

            msg=""
            for raw_msg in (
                row.get("wlan_rsna_eapol.keydes.msgnr"),
                row.get("eapol.keydes.msgnr"),
            ):
                candidate=first_value(raw_msg)
                if candidate in {"1","2","3","4"}:
                    msg=candidate
                    break
                match=re.search(r"(?:message\s*)?([1-4])(?:\s*(?:of|/)\s*4)?$", candidate, re.I)
                if match:
                    msg=match.group(1)
                    break

            if msg not in {"1","2","3","4"}:
                info=as_int(row.get("wlan_rsna_eapol.keydes.key_info"))
                ack=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.key_ack"))
                mic=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.key_mic"))
                install=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.install"))
                secure=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.secure"))
                request=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.request"))
                error=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.error"))
                key_type=as_flag(row.get("wlan_rsna_eapol.keydes.key_info.key_type"))
                if info is not None:
                    install=bool(info & 0x0040) if install is None else install
                    ack=bool(info & 0x0080) if ack is None else ack
                    mic=bool(info & 0x0100) if mic is None else mic
                    secure=bool(info & 0x0200) if secure is None else secure
                    error=bool(info & 0x0400) if error is None else error
                    request=bool(info & 0x0800) if request is None else request
                    key_type=bool(info & 0x0008) if key_type is None else key_type

                if request is True or error is True or key_type is False:
                    msg=""
                elif direction == "ap_to_sta" and ack is True and mic is False:
                    msg="1"
                elif direction == "ap_to_sta" and ack is True and mic is True:
                    msg="3"
                elif direction == "sta_to_ap" and ack is False and mic is True:
                    data_len=as_int(row.get("wlan_rsna_eapol.keydes.data_len"))
                    # Se Secure è esplicitamente vero è M4. Se Secure non è
                    # disponibile, data_len=0 è solo un indizio e non un errore.
                    if secure is True:
                        msg="4"
                    elif secure is False:
                        msg="2"
                    elif data_len == 0:
                        msg="4"
                    else:
                        msg="2"

            try:
                ts=float(first_value(row.get("frame.time_epoch")))
            except (TypeError, ValueError):
                ts=0.0
            frame_no=first_value(row.get("frame.number"))
            frames_by_sta.setdefault(sta, []).append({
                "ts":ts,
                "frame_no":frame_no,
                "msg":msg,
                "replay":as_int(row.get("wlan_rsna_eapol.keydes.replay_counter")),
                "nonce":first_value(row.get("wlan_rsna_eapol.keydes.nonce")),
            })
            self.logmsg(
                f"EAPOL frame {frame_no or '?'}: AP {bssid} <-> {sta} "
                f"dir={direction or '?'} " + (f"M{msg}" if msg else "M? non classificato")
            )

        self.logmsg(
            f"Diagnostica EAPOL: tshark={raw_eapol_lines}, accettati={accepted_eapol}, "
            f"scartati_senza_AP={discarded_no_ap}, scartati_senza_client={discarded_no_sta}."
        )

        pairs={}
        for sta,frames in frames_by_sta.items():
            frames.sort(key=lambda item:item["ts"])
            attempts=[]
            current=[]
            for frame in frames:
                if current and (
                    frame["ts"]-current[-1]["ts"] > 10.0
                    or (frame["msg"] == "1" and any(x["msg"] in {"2","3","4"} for x in current))
                ):
                    attempts.append(current)
                    current=[]
                current.append(frame)
            if current:
                attempts.append(current)

            best=None
            for attempt in attempts:
                ordered=[]
                for frame in attempt:
                    if frame["msg"] and (not ordered or frame["msg"] != ordered[-1]["msg"]):
                        ordered.append(frame)
                msgs={x["msg"] for x in ordered}
                sequence=[x["msg"] for x in ordered]
                complete=False
                try:
                    i1=sequence.index("1")
                    i2=sequence.index("2",i1+1)
                    i3=sequence.index("3",i2+1)
                    i4=sequence.index("4",i3+1)
                    chosen=[ordered[i] for i in (i1,i2,i3,i4)]
                    r1,r2,r3,r4=[x["replay"] for x in chosen]
                    replay_ok=(r1 is None or r2 is None or r1 == r2) and (
                        r3 is None or r4 is None or r3 == r4
                    ) and (r1 is None or r3 is None or r3 >= r1)
                    complete=replay_ok
                except ValueError:
                    pass
                rec={
                    "frames":len(attempt), "msgs":msgs,
                    "first_ts":attempt[0]["ts"], "last_ts":attempt[-1]["ts"],
                    "complete":complete,
                    # I quattro frame effettivamente usati per validare M1->M4.
                    # Servono per costruire una impronta stabile dell'handshake,
                    # invece di mostrare soltanto AP e CLIENT.
                    "chosen": chosen if complete else []
                }
                score=(1 if complete else 0,len(msgs),len(attempt))
                if best is None or score > best[0]:
                    best=(score,rec)
            if best:
                pairs[sta]=best[1]

        # PMKID: best effort, ma nessun errore grezzo viene mostrato nel riquadro.
        pmkid_found=False
        pmkid_value=""
        pmkid_filters=[
            ("wlan.rsn.pmkid", ["-e","wlan.rsn.pmkid"]),
            ("wlan_rsna_eapol.keydes.data", ["-e","wlan_rsna_eapol.keydes.data"]),
        ]
        for display_filter, extra in pmkid_filters:
            try:
                pcmd=["tshark","-r",str(cap),"-Y",display_filter,"-T","fields",
                      "-E","separator=/t","-E","occurrence=f","-e","wlan.bssid"] + extra
                pp=run(pcmd, timeout=5)
                if pp.returncode != 0:
                    continue
                for line in pp.stdout.splitlines():
                    vals=line.split("\t")
                    vals += [""]*(2-len(vals))
                    fb=vals[0].strip().lower()
                    val=vals[1].strip()
                    if fb and fb != bssid:
                        continue
                    if display_filter == "wlan_rsna_eapol.keydes.data":
                        compact=re.sub(r"[^0-9a-fA-F]", "", val).lower()
                        match=re.search(r"dd14000fac04([0-9a-f]{32})", compact)
                        val=match.group(1) if match else ""
                    if val:
                        pmkid_found=True
                        pmkid_value=val
                        break
                if pmkid_found:
                    break
            except Exception as e:
                self.logmsg(f"PMKID: controllo non disponibile: {e}")

        if pmkid_found:
            short=pmkid_value[:48] + ("..." if len(pmkid_value)>48 else "")
            self.root.after(0, self.pmkid_state.set, f"PMKID: OSSERVATO ({short})")
        else:
            self.root.after(0, self.pmkid_state.set, "PMKID: non osservato")

        if not pairs:
            # Un controllo successivo può leggere un PCAP parziale o diverso: se
            # un handshake completo è già stato trovato, non cancellare la GUI.
            if self.handshake_latched:
                return True
            self.root.after(0,self.handshake_state.set,self._handshake_word(False))
            self._set_handshake_parts(set())
            self._set_handshake_copy_enabled(False)
            self.root.after(0,self.handshake_string.set,"")
            if raw_eapol_lines == 0:
                self.logmsg("Handshake: ASSENTE - nessun EAPOL rilevato nella cattura")
            elif accepted_eapol == 0:
                self.logmsg(f"Handshake: ASSENTE - EAPOL presenti ({raw_eapol_lines}) ma non riferibili al BSSID selezionato")
            else:
                self.logmsg(f"Handshake: ASSENTE - EAPOL accettati={accepted_eapol}, M1-M4 non ancora ricostruibili")
            return False

        ranked=sorted(
            pairs.items(),
            key=lambda kv:(kv[1]["complete"],len(kv[1]["msgs"]),kv[1]["frames"]),
            reverse=True
        )
        sta,rec=ranked[0]
        msgs=rec["msgs"]
        progress_lines=[f"M{n} TROVATO" if n in msgs else f"M{n}: --" for n in ("1","2","3","4")]
        progress_text="   ".join(progress_lines)
        duration_txt=""
        if rec["first_ts"] is not None and rec["last_ts"] is not None:
            dt=max(0.0, rec["last_ts"]-rec["first_ts"])
            duration_txt=f" | {dt:.3f}s"

        if not msgs:
            if self.handshake_latched:
                return True
            self.root.after(0,self.handshake_state.set,self._handshake_word(False))
            self._set_handshake_parts(set())
            self._set_handshake_copy_enabled(False)
            self.root.after(0,self.handshake_string.set,"")
            self.logmsg(f"EAPOL rilevati per client {sta}, ma M1-M4 non classificabili")
            return False

        # Aggiorna progressivamente il riquadro solo finché non è stato
        # memorizzato un handshake completo. Dopo il completo la GUI resta fissa.
        if self.handshake_latched and not rec["complete"]:
            return True
        self.root.after(0,self.handshake_state.set,self._handshake_word(False))
        self._set_handshake_parts(msgs)
        self.root.after(0,self.handshake_string.set,"")
        self._set_handshake_copy_enabled(False)

        if rec["complete"]:
            key=(bssid,sta,"complete")
            if key not in self.handshake_pairs:
                self.handshake_pairs.add(key)
                self.logmsg(f"HANDSHAKE 4-way completo: AP {bssid} <-> client {sta}")

            # Mostra i dati REALI estratti dai quattro frame EAPOL usati per
            # confermare il 4-way handshake. Non generiamo più una SHA-256
            # artificiale: il riquadro e il pulsante COPIA riportano esattamente
            # messaggio, replay counter, nonce e timestamp osservati nel PCAP.
            chosen=rec.get("chosen") or []
            # Non inventiamo una "stringa handshake": il formato standard
            # della cattura resta il file PCAP prodotto da airodump-ng.
            # Quando il 4-way è completo, mostriamo e copiamo il riferimento
            # al PCAP reale che contiene i frame EAPOL originali.
            # Rappresentazione testuale unica dei dati effettivamente osservati
            # nel 4-way handshake confermato. Non mostra il percorso del PCAP.
            # La stringa concatena i campi EAPOL già estratti dai frame scelti.
            parts=[]
            for item in (rec.get("chosen") or []):
                parts.append(
                    "M%s:R=%s:N=%s" % (
                        item.get("msg",""),
                        "n/d" if item.get("replay") is None else item.get("replay"),
                        (item.get("nonce") or "n/d").strip().lower(),
                    )
                )
            handshake_text=" | ".join(parts)
            self.handshake_latched=True
            self.handshake_latched_text=handshake_text
            self.handshake_latched_msgs={"1","2","3","4"}
            # Handshake completo: conferma M1-M4 e mostra TROVATO lampeggiante.
            self._set_handshake_parts({"1","2","3","4"})
            self.root.after(0,self.handshake_state.set,self._handshake_word(True))
            # Mantiene visibili gli stati M1/M2/M3/M4 già ricavati dal PCAP.
            self.root.after(0,self.handshake_string.set,"TROVATO")
            self._show_handshake_found_only()
            self._set_handshake_copy_enabled(True)
            self.handshake_found_async=True
            # La spunta "termina se trovi handshake" deve avere effetto
            # esclusivamente durante DISTURBO. La cattura passiva continua sempre
            # fino al tempo impostato, pur continuando a rilevare/mostrare l'handshake.
            if stop_on_found and self.stop_on_handshake_event.is_set():
                self.diegi_stop.set()
                self.capture_stop.set()
                self.root.after(0, self._stop_all_on_handshake)
            self.root.after(0, self.handshake_state.set, self._handshake_word(True))
            return True

        return False


    def _handshake_word(self, found=False):
        """Restituisce lo stato HANDSHAKE nella lingua corrente."""
        if getattr(self, "language", "it") == "en":
            return "FOUND" if found else "ABSENT"
        return "TROVATO" if found else "ASSENTE"

    def _handshake_part_word(self, found=False):
        """Stato M1-M4 nella lingua corrente."""
        if getattr(self, "language", "it") == "en":
            return "FOUND" if found else "--"
        return "TROVATO" if found else "--"

    def _show_handshake_found_only(self):
        """Mantiene M1/M2/M3/M4 visibili e fa lampeggiare TROVATO sotto M4."""
        def apply():
            try:
                self.handshake_state.set(self._handshake_word(True))
                if getattr(self, "handshake_state_label", None) is not None:
                    self.handshake_state_label.grid(
                        row=5, column=0, columnspan=2,
                        sticky="ew", padx=4, pady=(2,4)
                    )
                self._start_handshake_found_blink()
            except Exception:
                pass
        self.root.after(0, apply)

    def _start_handshake_found_blink(self):
        """Lampeggia TROVATO/FOUND solo in rosso, grande e grassetto, senza muovere il layout."""
        self._stop_handshake_found_blink()
        self._handshake_blink_phase = False

        def tick():
            try:
                label=getattr(self,"handshake_state_label",None)
                if label is None or self.handshake_state.get() != self._handshake_word(True):
                    self._handshake_blink_after=None
                    return

                self._handshake_blink_phase = not getattr(
                    self,"_handshake_blink_phase",False
                )

                # Sempre grande e in grassetto.
                label.configure(font=("TkDefaultFont",15,"bold"))

                if self._handshake_blink_phase:
                    # Fase visibile: esclusivamente ROSSO.
                    label.configure(
                        foreground=("#8E3030" if getattr(self, "night_mode", False) else "#ff0000")
                    )
                else:
                    # Fase invisibile senza rimuovere il widget: usa il colore
                    # dello sfondo del Label, così la geometria resta immutata.
                    try:
                        bg=label.cget("background")
                        label.configure(foreground=bg)
                    except Exception:
                        # Fallback neutro se il tema ttk non espone background.
                        label.configure(foreground="#f0f0f0")

                self._handshake_blink_after=self.root.after(450,tick)
            except Exception:
                self._handshake_blink_after=None

        # Parte subito con TROVATO/FOUND ben visibile in rosso.
        try:
            label=getattr(self,"handshake_state_label",None)
            if label is not None:
                label.configure(
                    font=("TkDefaultFont",15,"bold"),
                    foreground=("#8E3030" if getattr(self, "night_mode", False) else "#ff0000")
                )
        except Exception:
            pass
        self._handshake_blink_after=self.root.after(450,tick)

    def _stop_handshake_found_blink(self):
        """Ferma il lampeggio senza modificare geometria o visibilità del widget."""
        aid = getattr(self, "_handshake_blink_after", None)
        if aid is not None:
            try:
                self.root.after_cancel(aid)
            except Exception:
                pass

        self._handshake_blink_after = None
        self._handshake_blink_phase = False

        try:
            label = getattr(self, "handshake_state_label", None)
            if label is not None:
                # Ripristina un colore neutro coerente col tema.
                if getattr(self, "night_mode", False):
                    label.configure(font=("TkDefaultFont",15,"bold"),foreground="#d6d8dc")
                else:
                    label.configure(font=("TkDefaultFont",15,"bold"),foreground="#000000")
        except Exception:
            pass
        self._handshake_blink_after=None
        try:
            label=getattr(self,"handshake_state_label",None)
            if label is not None:
                label.grid()
        except Exception:
            pass

    def _restore_handshake_panel_layout(self):
        """Mantiene M1/M2/M3/M4 visibili e mostra ASSENTE in grassetto sotto tutti."""
        def apply():
            try:
                self._stop_handshake_found_blink()
                self.handshake_state.set(self._handshake_word(False))
                if getattr(self, "handshake_state_label", None) is not None:
                    self.handshake_state_label.grid(
                        row=5, column=0, columnspan=2,
                        sticky="ew", padx=4, pady=(2,4)
                    )
            except Exception:
                pass
        self.root.after(0, apply)


    def _capture_chain_ensure(self):
        """Inizializza la sessione che unisce catture consecutive correlate."""
        if not isinstance(getattr(self, "_capture_chain_expected_targets", None), dict):
            self._capture_chain_expected_targets = {}
        if not isinstance(getattr(self, "_capture_chain_targets", None), list):
            self._capture_chain_targets = []
        if not isinstance(getattr(self, "_capture_chain_segment_count", None), int):
            self._capture_chain_segment_count = 0
        if not hasattr(self, "_capture_chain_archive_path"):
            self._capture_chain_archive_path = ""
        if not hasattr(self, "_capture_chain_session_stamp"):
            self._capture_chain_session_stamp = ""
        if not hasattr(self, "_capture_chain_current_continuation"):
            self._capture_chain_current_continuation = False
        if not hasattr(self, "_capture_chain_current_reason"):
            self._capture_chain_current_reason = ""
        if not hasattr(self, "_capture_chain_current_target"):
            self._capture_chain_current_target = ""


    def _capture_chain_prepare_start(self, bssid):
        """Decide se AVVIA apre una nuova cattura o continua una multi-scansione.

        Una continuazione è ammessa solo se il BSSID è stato proposto dal sistema
        come seconda scansione (router in cascata, doppia banda o future relazioni).
        In quel caso il nuovo segmento verrà aggiunto allo STESSO PCAP definitivo.
        """
        self._capture_chain_ensure()
        target = str(bssid or "").strip().lower()
        expected = self._capture_chain_expected_targets
        reason = str(expected.get(target, "") or "")
        archive = Path(str(getattr(self, "_capture_chain_archive_path", "") or ""))
        can_continue = bool(reason and archive.exists())

        if can_continue:
            self._capture_chain_current_continuation = True
            self._capture_chain_current_reason = reason
            try:
                expected.pop(target, None)
            except Exception:
                pass
            try:
                self.logmsg(
                    ("CONTINUAZIONE MULTI-SCAN: " if getattr(self, "language", "it") != "en"
                     else "MULTI-SCAN CONTINUATION: ")
                    + f"{target} | {reason} | PCAP {archive.name}"
                )
            except Exception:
                pass
        else:
            # Nuovo AVVIA non correlato: apre una nuova sessione. Il precedente
            # PCAP resta archiviato ma non verrà mescolato con questa cattura.
            self._capture_chain_expected_targets = {}
            self._capture_chain_targets = []
            self._capture_chain_segment_count = 0
            self._capture_chain_archive_path = ""
            self._capture_chain_session_stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            self._capture_chain_current_continuation = False
            self._capture_chain_current_reason = ""

        self._capture_chain_current_target = target


    def _capture_chain_register_expected_second_scan(self, target_bssid, reason):
        """Registra un BSSID che, se catturato subito dopo, appartiene allo stesso PCAP."""
        self._capture_chain_ensure()
        target = str(target_bssid or "").strip().lower()
        if not MAC_FULL.match(target):
            return
        self._capture_chain_expected_targets[target] = str(reason or "second_scan")
        try:
            self.logmsg(
                ("Seconda cattura collegata registrata: " if getattr(self, "language", "it") != "en"
                 else "Linked second capture registered: ")
                + f"{target} ({reason})"
            )
        except Exception:
            pass


    def _merge_classic_pcap(self, first_path, second_path, dest_path):
        """Unisce due PCAP classici mantenendo un solo global header.

        airodump-ng con --output-format pcap produce normalmente questo formato.
        I due segmenti sono sequenziali, quindi l'ordine dei pacchetti è già corretto.
        """
        first_path = Path(first_path)
        second_path = Path(second_path)
        dest_path = Path(dest_path)
        tmp = dest_path.with_name(dest_path.name + ".merge_tmp")
        try:
            with first_path.open("rb") as f1, second_path.open("rb") as f2:
                h1 = f1.read(24)
                h2 = f2.read(24)
                if len(h1) != 24 or len(h2) != 24:
                    return False
                classic_magics = {
                    b"\xd4\xc3\xb2\xa1", b"\xa1\xb2\xc3\xd4",
                    b"\x4d\x3c\xb2\xa1", b"\xa1\xb2\x3c\x4d",
                }
                if h1[:4] not in classic_magics or h2[:4] not in classic_magics:
                    return False
                # Stesso endian/formato e stesso link-layer type.
                if h1[:4] != h2[:4] or h1[20:24] != h2[20:24]:
                    return False

                with tmp.open("wb") as out:
                    out.write(h1)
                    shutil.copyfileobj(f1, out, length=1024 * 1024)
                    shutil.copyfileobj(f2, out, length=1024 * 1024)

            if not tmp.exists() or tmp.stat().st_size <= 24:
                return False
            os.replace(str(tmp), str(dest_path))
            return True
        except Exception:
            try:
                tmp.unlink(missing_ok=True)
            except Exception:
                pass
            return False


    def _merge_capture_files(self, existing_path, new_path):
        """Aggiunge new_path al PCAP definitivo esistente senza creare un secondo archivio."""
        existing_path = Path(existing_path)
        new_path = Path(new_path)
        if not existing_path.exists() or not new_path.exists():
            return False

        # Percorso principale: merge nativo per i PCAP classici di airodump-ng.
        if self._merge_classic_pcap(existing_path, new_path, existing_path):
            return True

        # Fallback per eventuali formati futuri: usa mergecap se installato.
        mergecap = shutil.which("mergecap")
        if not mergecap:
            return False
        tmp = existing_path.with_name(existing_path.name + ".mergecap_tmp")
        try:
            r = run([
                mergecap, "-w", str(tmp), str(existing_path), str(new_path)
            ], timeout=120)
            if r.returncode == 0 and tmp.exists() and tmp.stat().st_size > 0:
                os.replace(str(tmp), str(existing_path))
                return True
        except Exception:
            pass
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass
        return False

    def _archive_capture(self, cap, capture_kind):
        """
        Archivia il PCAP definitivo nella cartella CATTURE.

        Per le CATTURE PASSIVE collegate tra loro dal sistema (router in cascata,
        doppia banda, ecc.) viene mantenuto UN SOLO FILE: il secondo segmento e gli
        eventuali successivi vengono accodati al PCAP della prima scansione.
        """
        cap = Path(cap)
        if not cap.exists():
            return None

        if capture_kind == "manual":
            prefix = "CATTURA"
        elif capture_kind == "handshake" and self.handshake_latched:
            prefix = "HANDSHAKE"
        else:
            return None

        # Il merge multi-scan riguarda solo la cattura passiva/manuale.
        if capture_kind == "manual":
            self._capture_chain_ensure()
            existing_s = str(getattr(self, "_capture_chain_archive_path", "") or "")
            existing = Path(existing_s) if existing_s else None
            continuation = bool(getattr(self, "_capture_chain_current_continuation", False))

            if continuation and existing is not None and existing.exists():
                if self._merge_capture_files(existing, cap):
                    self._capture_chain_segment_count = int(
                        getattr(self, "_capture_chain_segment_count", 1) or 1
                    ) + 1
                    target = str(getattr(self, "_capture_chain_current_target", "") or "")
                    if target and target not in self._capture_chain_targets:
                        self._capture_chain_targets.append(target)
                    self.capture_file = existing
                    try:
                        self.logmsg(
                            ("PCAP multi-scansione aggiornato: "
                             if getattr(self, "language", "it") != "en"
                             else "Multi-scan PCAP updated: ")
                            + f"{existing} | segmenti={self._capture_chain_segment_count}"
                        )
                    except Exception:
                        pass
                    return existing

                # Non creare silenziosamente un secondo CATTURA_*.pcap: in caso
                # di merge impossibile segnala l'errore e conserva il primo file.
                try:
                    self.logmsg(
                        ("ERRORE: impossibile unire la seconda cattura al PCAP multi-scansione. "
                         "Nessun secondo file archiviato."
                         if getattr(self, "language", "it") != "en"
                         else "ERROR: unable to merge the second capture into the multi-scan PCAP. "
                              "No second archive file was created.")
                    )
                except Exception:
                    pass
                self.capture_file = existing
                return None

        stamp = datetime.now().strftime("%d-%m-%y__%H-%M-%S")
        dest = self.captures_dir / f"{prefix}_{stamp}.pcap"
        if dest.exists():
            stamp = datetime.now().strftime("%d-%m-%y__%H-%M-%S_%f")
            dest = self.captures_dir / f"{prefix}_{stamp}.pcap"

        try:
            shutil.copy2(cap, dest)
            self.capture_file = dest

            if capture_kind == "manual":
                self._capture_chain_archive_path = str(dest)
                self._capture_chain_segment_count = 1
                target = str(getattr(self, "_capture_chain_current_target", "") or "")
                self._capture_chain_targets = [target] if target else []
                if not str(getattr(self, "_capture_chain_session_stamp", "") or ""):
                    self._capture_chain_session_stamp = datetime.now().strftime("%Y%m%d_%H%M%S")

            self.logmsg(f"PCAP archiviato: {dest}")
            return dest
        except Exception as e:
            self.logmsg(f"Errore archiviazione PCAP in CATTURE: {e}")
            return None

    def _set_handshake_parts(self, msgs):
        """Aggiorna M1-M4; un completo già trovato resta memorizzato a video."""
        found=set(str(x) for x in (msgs or set()))
        if self.handshake_latched:
            # Handshake completo: M1-M4 restano visibili e confermati.
            self.root.after(0, self.handshake_m1.set, self._handshake_part_word(True))
            self.root.after(0, self.handshake_m2.set, self._handshake_part_word(True))
            self.root.after(0, self.handshake_m3.set, self._handshake_part_word(True))
            self.root.after(0, self.handshake_m4.set, self._handshake_part_word(True))
            return
        self.root.after(0, self.handshake_m1.set, self._handshake_part_word("1" in found))
        self.root.after(0, self.handshake_m2.set, self._handshake_part_word("2" in found))
        self.root.after(0, self.handshake_m3.set, self._handshake_part_word("3" in found))
        self.root.after(0, self.handshake_m4.set, self._handshake_part_word("4" in found))

    def _set_handshake_copy_enabled(self, enabled):
        """
        Abilita ESPORTA HANDSHAKE solo quando esiste realmente un 4-way handshake
        completo. Vale sia per DISTURBO sia per CATTURA PASSIVA.
        """
        real_enabled = bool(enabled and getattr(self, "handshake_latched", False))

        def apply():
            btn = getattr(self, "export_handshake_button", None)
            if btn is None:
                return
            try:
                btn.configure(state=("normal" if real_enabled else "disabled"))
            except Exception:
                pass

        self.root.after(0, apply)

    def _reset_handshake_panel(self):
        self._restore_handshake_panel_layout()
        self.handshake_latched=False
        self.handshake_latched_text=""
        self.handshake_latched_msgs=set()
        self.root.after(0, self.handshake_state.set, self._handshake_word(False))
        self._set_handshake_parts(set())
        self.root.after(0, self.handshake_string.set, "")
        self._set_handshake_copy_enabled(False)


    def export_capture_file(self):
        """
        Mostra i file presenti nella cartella CATTURE e permette di copiarne
        uno in una cartella scelta dall'utente sul PC.
        """
        try:
            self.captures_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.set_status(f"Impossibile accedere alla cartella CATTURE: {e}")
            return

        files=sorted(
            [p for p in self.captures_dir.iterdir() if p.is_file()],
            key=lambda p:p.stat().st_mtime,
            reverse=True
        )

        if not files:
            self.set_status("La cartella CATTURE è vuota.")
            return

        # Evita più finestre ESPORTA sovrapposte.
        try:
            _old_export = getattr(self, "_export_capture_window", None)
            if _old_export is not None and _old_export.winfo_exists():
                try:
                    _old_export.grab_release()
                except Exception:
                    pass
                _old_export.destroy()
        except Exception:
            pass

        # ESPORTA è ora completamente INTERNO alla finestra principale.
        # Non viene creato alcun tk.Toplevel: il window manager di Kali/Linux
        # non riceve una nuova finestra e quindi non può mostrare pannello,
        # icone del desktop o decorazioni di sistema.
        dark = bool(getattr(self, "night_mode", False))
        export_bg = "#12171B" if dark else "#ECEFF1"
        export_border = "#FFFFFF" if dark else "#202020"

        win = tk.Frame(
            self.root,
            bg=export_bg,
            highlightthickness=2,
            highlightbackground=export_border,
            highlightcolor=export_border,
            bd=0
        )
        self._export_capture_window = win

        export_w = 912
        export_h = 504
        self.root.update_idletasks()
        rw = max(800, int(self.root.winfo_width()))
        rh = max(600, int(self.root.winfo_height()))
        export_w = min(export_w, max(700, rw - 40))
        export_h = min(export_h, max(420, rh - 40))
        export_x = max(0, (rw - export_w) // 2)
        export_y = max(0, (rh - export_h) // 2)
        win.place(x=export_x, y=export_y, width=export_w, height=export_h)
        win.lift()

        def _enforce_export_no_wm(_event=None):
            # Compatibilità con il vecchio flusso: essendo un Frame interno
            # basta riportarlo sopra gli altri widget.
            try:
                win.lift()
            except Exception:
                pass

        def _close_export_window(_event=None):
            try:
                _dlg = getattr(self, "_export_save_dialog", None)
                if _dlg is not None and _dlg.winfo_exists():
                    try:
                        _dlg.grab_release()
                    except Exception:
                        pass
                    _dlg.destroy()
            except Exception:
                pass
            self._export_save_dialog = None
            try:
                win.grab_release()
            except Exception:
                pass
            try:
                win.destroy()
            except Exception:
                pass
            self._export_capture_window = None
            try:
                if self.root.winfo_exists():
                    self.root.lift()
                    self.root.focus_force()
            except Exception:
                pass

        try:
            win.bind("<Escape>", _close_export_window)
        except Exception:
            pass

        top=ttk.Frame(win,padding=3)
        top.pack(fill="x")
        ttk.Label(
            top,
            text=f"Cartella CATTURE: {self.captures_dir}",
            font=("TkDefaultFont",10,"bold")
        ).pack(anchor="w")

        body=ttk.Frame(win,padding=(3,0,3,3))
        body.pack(fill="both",expand=True)

        tree=ttk.Treeview(
            body,
            columns=("name","size","modified"),
            show="headings",
            selectmode="browse"
        )
        tree.heading("name",text="FILE")
        tree.heading("size",text="DIMENSIONE")
        tree.heading("modified",text="DATA / ORA")
        tree.column("name",width=420,anchor="w")
        tree.column("size",width=110,anchor="e")
        tree.column("modified",width=160,anchor="center")

        scroll=ttk.Scrollbar(body,orient="vertical",command=tree.yview)
        tree.configure(yscrollcommand=scroll.set)
        tree.pack(side="left",fill="both",expand=True)
        scroll.pack(side="right",fill="y")

        file_map={}
        for idx,p in enumerate(files):
            try:
                st=p.stat()
                size=f"{st.st_size/1024:.1f} KB"
                modified=datetime.fromtimestamp(st.st_mtime).strftime("%d/%m/%Y %H:%M:%S")
            except Exception:
                size=""
                modified=""
            iid=str(idx)
            file_map[iid]=p
            tree.insert("", "end", iid=iid, values=(p.name,size,modified))

        buttons=ttk.Frame(win,padding=(10,0,10,10))
        buttons.pack(fill="x")

        export_notice = tk.StringVar(value="")
        notice_label = ttk.Label(win, textvariable=export_notice, anchor="w")
        notice_label.pack(fill="x", padx=10, pady=(0,4))

        def _export_notice(message):
            try:
                export_notice.set(str(message))
                win.lift()
            except Exception:
                pass
            try:
                self.set_status(str(message))
            except Exception:
                pass

        def do_export():
            sel=tree.selection()
            if not sel:
                _export_notice("Seleziona prima un file.")
                return
            src_file=file_map.get(sel[0])
            if not src_file or not src_file.exists():
                _export_notice("Il file selezionato non è più disponibile.")
                return


            def _real_user_home():
                """HOME dell'utente grafico anche quando il programma gira con sudo."""
                user=(os.environ.get("SUDO_USER") or os.environ.get("USER") or "").strip()
                try:
                    import pwd
                    if user and user != "root":
                        return Path(pwd.getpwnam(user).pw_dir)
                except Exception:
                    pass
                return Path.home()

            def _desktop_folder():
                """Desktop/Scrivania configurato dal sistema per l'utente reale."""
                home=_real_user_home()

                # Rispetta XDG_DESKTOP_DIR, quindi funziona anche con Desktop
                # localizzato (es. Scrivania).
                try:
                    cfg=home / ".config" / "user-dirs.dirs"
                    if cfg.exists():
                        for line in cfg.read_text(encoding="utf-8",errors="ignore").splitlines():
                            if line.startswith("XDG_DESKTOP_DIR="):
                                value=line.split("=",1)[1].strip().strip('"')
                                value=value.replace("$HOME",str(home))
                                p=Path(value).expanduser()
                                if p.is_dir():
                                    return p
                except Exception:
                    pass

                for p in (home/"Desktop",home/"Scrivania"):
                    if p.is_dir():
                        return p
                return home

            def _usb_export_folder():
                """
                Individua una chiavetta USB anche quando il programma gira con sudo.
                Se il dispositivo USB è presente ma non ancora montato, prova a
                montarlo tramite udisksctl come utente grafico e poi lo ricerca di nuovo.
                """
                user=(os.environ.get("SUDO_USER") or os.environ.get("USER") or "").strip()
                found=[]

                def add(path):
                    try:
                        if not path:
                            return
                        p=Path(str(path).replace("\\040"," "))
                        if p.is_dir() and os.path.ismount(p):
                            s=str(p.resolve())
                            if s not in ("/","/boot","/boot/efi") and s not in [str(x) for x in found]:
                                found.append(Path(s))
                    except Exception:
                        pass

                def scan_mounts():
                    # A) Directory usate normalmente da Kali/GVFS/UDisks.
                    roots=[]
                    if user:
                        roots += [Path("/media")/user, Path("/run/media")/user]
                    roots += [Path("/media"), Path("/run/media"), Path("/mnt")]

                    for root in roots:
                        try:
                            if not root.is_dir():
                                continue
                            for p in root.rglob("*"):
                                if p.is_dir() and os.path.ismount(p):
                                    add(p)
                        except Exception:
                            pass

                    # B) findmnt: fonte affidabile dei filesystem realmente montati.
                    try:
                        p=subprocess.run(
                            ["findmnt","-rn","-o","SOURCE,TARGET"],
                            text=True,capture_output=True,timeout=4,check=False
                        )
                        for line in (p.stdout or "").splitlines():
                            parts=line.split(None,1)
                            if len(parts)!=2:
                                continue
                            dev,mp=parts
                            if dev.startswith("/dev/") and (
                                mp.startswith("/media/")
                                or mp.startswith("/run/media/")
                                or mp.startswith("/mnt/")
                            ):
                                add(mp)
                    except Exception:
                        pass

                    # C) lsblk: identifica esplicitamente bus USB e dispositivi rimovibili.
                    usb_parts=[]
                    try:
                        p=subprocess.run(
                            ["lsblk","-J","-p","-o",
                             "NAME,PATH,RM,HOTPLUG,TRAN,TYPE,FSTYPE,MOUNTPOINT,MOUNTPOINTS"],
                            text=True,capture_output=True,timeout=5,check=False
                        )
                        if p.returncode==0 and p.stdout.strip():
                            data=json.loads(p.stdout)

                            def walk(nodes,parent_usb=False,parent_removable=False):
                                for dev in nodes or []:
                                    tran=str(dev.get("tran") or "").lower()
                                    rm=str(dev.get("rm") or "0").lower() in ("1","true")
                                    hot=str(dev.get("hotplug") or "0").lower() in ("1","true")
                                    usb=parent_usb or tran=="usb"
                                    removable=parent_removable or rm or hot
                                    dtype=str(dev.get("type") or "")
                                    fstype=str(dev.get("fstype") or "")
                                    path=dev.get("path") or dev.get("name")

                                    mounts=[]
                                    mp=dev.get("mountpoint")
                                    if mp:
                                        mounts.append(mp)
                                    mps=dev.get("mountpoints") or []
                                    if isinstance(mps,str):
                                        mps=[mps]
                                    mounts += [x for x in mps if x]

                                    if usb or removable:
                                        for m in mounts:
                                            add(m)
                                        if dtype=="part" and fstype and not mounts and path:
                                            usb_parts.append(str(path))

                                    walk(dev.get("children") or [],usb,removable)

                            walk(data.get("blockdevices") or [])
                    except Exception:
                        usb_parts=[]

                    return usb_parts

                # Prima scansione.
                unmounted_usb_parts=scan_mounts()
                if found:
                    preferred=[
                        p for p in found
                        if user and (
                            str(p).startswith(f"/media/{user}/")
                            or str(p).startswith(f"/run/media/{user}/")
                        )
                    ]
                    return (preferred or found)[0]

                # USB presente ma non montata: prova udisksctl come utente reale.
                if unmounted_usb_parts and shutil.which("udisksctl"):
                    for dev in unmounted_usb_parts:
                        try:
                            if user and user!="root" and shutil.which("sudo"):
                                cmd=["sudo","-u",user,"udisksctl","mount","-b",dev]
                            else:
                                cmd=["udisksctl","mount","-b",dev]
                            subprocess.run(
                                cmd,text=True,capture_output=True,
                                timeout=12,check=False
                            )
                        except Exception:
                            pass

                    time.sleep(0.8)
                    found.clear()
                    scan_mounts()

                if not found:
                    return None

                preferred=[
                    p for p in found
                    if user and (
                        str(p).startswith(f"/media/{user}/")
                        or str(p).startswith(f"/run/media/{user}/")
                    )
                ]
                return (preferred or found)[0]

            # Se c'è una USB montata, il dialogo si apre direttamente lì.
            # In assenza di USB si apre sul Desktop/Scrivania del sistema.
            initial_dir=_usb_export_folder() or _desktop_folder()

            def _themed_save_dialog(source_file, start_dir):
                """Dialogo di salvataggio interno che segue realmente tema giorno/notte."""
                dark = bool(getattr(self, "night_mode", False))

                bg = "#000000" if dark else "#F0F0F0"
                panel_bg = "#090909" if dark else "#FFFFFF"
                fg = "#D8D8D8" if dark else "#000000"
                muted = "#9A9A9A" if dark else "#555555"
                entry_bg = "#101010" if dark else "#FFFFFF"
                select_bg = "#2B3F55" if dark else "#3478BF"
                select_fg = "#FFFFFF"
                btn_bg = "#181818" if dark else "#E7E7E7"
                btn_active = "#303030" if dark else "#D5D5D5"
                border = "#3A3A3A" if dark else "#B7B7B7"

                # Chiude un eventuale selettore rimasto aperto da un tentativo precedente.
                try:
                    _old_dlg = getattr(self, "_export_save_dialog", None)
                    if _old_dlg is not None and _old_dlg.winfo_exists():
                        try:
                            _old_dlg.grab_release()
                        except Exception:
                            pass
                        _old_dlg.destroy()
                except Exception:
                    pass

                # Selettore destinazione COMPLETAMENTE INTERNO alla GUI.
                # Nessun Toplevel = nessuna barra/icone/pannello del desktop.
                dlg = tk.Frame(
                    self.root,
                    bg=bg,
                    highlightthickness=2,
                    highlightbackground=border,
                    highlightcolor=border,
                    bd=0
                )
                self._export_save_dialog = dlg

                self.root.update_idletasks()
                rw2 = max(800, int(self.root.winfo_width()))
                rh2 = max(600, int(self.root.winfo_height()))
                ww = min(820, max(680, rw2 - 60))
                hh = min(560, max(450, rh2 - 60))
                xx = max(0, (rw2 - ww) // 2)
                yy = max(0, (rh2 - hh) // 2)
                dlg.place(x=xx, y=yy, width=ww, height=hh)
                dlg.lift()

                def _enforce_save_no_wm(_event=None):
                    try:
                        dlg.lift()
                    except Exception:
                        pass

                result = {"path": None}
                current_dir = [Path(start_dir).expanduser()]

                topbar = tk.Frame(dlg, bg=bg)
                topbar.pack(fill="x", padx=10, pady=(10,6))

                tk.Label(
                    topbar, text="CARTELLA:", bg=bg, fg=fg,
                    font=("TkDefaultFont", 10, "bold")
                ).pack(side="left", padx=(0,6))

                path_var = tk.StringVar(value=str(current_dir[0]))
                path_entry = tk.Entry(
                    topbar, textvariable=path_var,
                    bg=entry_bg, fg=fg, insertbackground=fg,
                    relief="solid", bd=1,
                    highlightthickness=1,
                    highlightbackground=border,
                    highlightcolor=border
                )
                path_entry.pack(side="left", fill="x", expand=True)

                def _button(parent, text, cmd, width=None):
                    return tk.Button(
                        parent, text=text, command=cmd, width=width,
                        bg=btn_bg, fg=fg,
                        activebackground=btn_active,
                        activeforeground=fg,
                        relief="raised", bd=2,
                        highlightthickness=0,
                        cursor="hand2"
                    )

                nav = tk.Frame(dlg, bg=bg)
                nav.pack(fill="x", padx=10, pady=(0,6))

                list_frame = tk.Frame(
                    dlg, bg=panel_bg,
                    highlightthickness=1,
                    highlightbackground=border
                )
                list_frame.pack(fill="both", expand=True, padx=10, pady=(0,8))

                folder_list = tk.Listbox(
                    list_frame,
                    bg=panel_bg, fg=fg,
                    selectbackground=select_bg,
                    selectforeground=select_fg,
                    activestyle="none",
                    relief="flat", bd=0,
                    highlightthickness=0,
                    font=("TkDefaultFont", 10)
                )
                yscroll = tk.Scrollbar(
                    list_frame, orient="vertical",
                    command=folder_list.yview,
                    bg=btn_bg, troughcolor=panel_bg,
                    activebackground=btn_active,
                    highlightthickness=0
                )
                folder_list.configure(yscrollcommand=yscroll.set)
                folder_list.pack(side="left", fill="both", expand=True, padx=(4,0), pady=4)
                yscroll.pack(side="right", fill="y", padx=(0,4), pady=4)

                entries = []

                def refresh_folder():
                    nonlocal entries
                    try:
                        p = Path(path_var.get()).expanduser()
                        if not p.is_dir():
                            p = current_dir[0]
                        p = p.resolve()
                    except Exception:
                        p = current_dir[0]

                    current_dir[0] = p
                    path_var.set(str(p))
                    folder_list.delete(0, "end")
                    entries = []

                    try:
                        dirs = []
                        files_local = []
                        for item in p.iterdir():
                            try:
                                if item.is_dir():
                                    dirs.append(item)
                                elif item.is_file():
                                    files_local.append(item)
                            except Exception:
                                pass
                        dirs.sort(key=lambda x: x.name.lower())
                        files_local.sort(key=lambda x: x.name.lower())

                        for item in dirs:
                            entries.append(("dir", item))
                            folder_list.insert("end", "📁  " + item.name)
                        for item in files_local:
                            entries.append(("file", item))
                            folder_list.insert("end", "     " + item.name)
                    except Exception as e:
                        _export_notice(f"Impossibile leggere la cartella: {e}")

                def go_up():
                    try:
                        parent = current_dir[0].parent
                        path_var.set(str(parent))
                        refresh_folder()
                    except Exception:
                        pass

                def go_home():
                    path_var.set(str(_real_user_home()))
                    refresh_folder()

                def go_desktop():
                    path_var.set(str(_desktop_folder()))
                    refresh_folder()

                def open_selected(_event=None):
                    sel = folder_list.curselection()
                    if not sel:
                        return
                    kind, item = entries[sel[0]]
                    if kind == "dir":
                        path_var.set(str(item))
                        refresh_folder()
                    else:
                        filename_var.set(item.name)

                folder_list.bind("<Double-Button-1>", open_selected)
                path_entry.bind("<Return>", lambda _e: refresh_folder())

                _button(nav, "SU", go_up, 8).pack(side="left", padx=(0,6))
                _button(nav, "HOME", go_home, 8).pack(side="left", padx=(0,6))
                _button(nav, "DESKTOP", go_desktop, 10).pack(side="left")

                bottom = tk.Frame(dlg, bg=bg)
                bottom.pack(fill="x", padx=10, pady=(0,10))

                tk.Label(
                    bottom, text="NOME FILE:", bg=bg, fg=fg,
                    font=("TkDefaultFont", 10, "bold")
                ).pack(side="left", padx=(0,6))

                filename_var = tk.StringVar(value=source_file.name)
                filename_entry = tk.Entry(
                    bottom, textvariable=filename_var,
                    bg=entry_bg, fg=fg, insertbackground=fg,
                    relief="solid", bd=1,
                    highlightthickness=1,
                    highlightbackground=border,
                    highlightcolor=border,
                    width=36
                )
                filename_entry.pack(side="left", fill="x", expand=True, padx=(0,8))

                def cancel(_event=None):
                    result["path"] = None
                    try:
                        dlg.grab_release()
                    except Exception:
                        pass
                    try:
                        dlg.destroy()
                    except Exception:
                        pass
                    self._export_save_dialog = None
                    try:
                        if win.winfo_exists():
                            _enforce_export_no_wm()
                            win.focus_set()
                    except Exception:
                        pass

                def save_here():
                    name = (filename_var.get() or "").strip()
                    if not name:
                        _export_notice("Inserisci un nome file.")
                        return

                    dest_path = current_dir[0] / name
                    if dest_path.exists():
                        _export_notice(
                            f"Il file esiste già: {dest_path}. "
                            "Cambia nome oppure elimina prima il file esistente."
                        )
                        return

                    result["path"] = str(dest_path)
                    try:
                        dlg.grab_release()
                    except Exception:
                        pass
                    try:
                        dlg.destroy()
                    except Exception:
                        pass
                    self._export_save_dialog = None

                _button(bottom, "ANNULLA", cancel, 10).pack(side="right")
                _button(bottom, "SALVA", save_here, 10).pack(side="right", padx=(0,6))

                try:
                    dlg.bind("<Escape>", cancel)
                except Exception:
                    pass
                refresh_folder()

                # NESSUN grab_set(): il grab globale rendeva talvolta irraggiungibile
                # il pulsante ESCI e dava l'impressione che tutta la GUI fosse bloccata.
                # wait_window mantiene il flusso del dialogo ma continua a processare
                # gli eventi Tk, lasciando la finestra principale utilizzabile.
                try:
                    filename_entry.focus_set()
                    filename_entry.selection_range(0, "end")
                    dlg.wait_window()
                except Exception:
                    pass
                finally:
                    self._export_save_dialog = None

                return result["path"]

            dest = _themed_save_dialog(src_file, initial_dir)

            # Il window manager può rimappare la finestra padre quando il dialogo
            # figlio si chiude: riapplichiamo sempre la modalità senza decorazioni.
            try:
                if win.winfo_exists():
                    _enforce_export_no_wm()
                    win.focus_set()
            except Exception:
                pass

            if not dest:
                return

            try:
                shutil.copy2(src_file, dest)
                _export_notice(f"File esportato correttamente: {dest}")
            except Exception as e:
                _export_notice(f"Errore durante l'esportazione: {e}")

        ttk.Button(buttons,text="ESPORTA FILE SELEZIONATO",command=do_export).pack(side="left")
        ttk.Button(buttons,text="CHIUDI",command=_close_export_window).pack(side="right")

        if files:
            tree.selection_set("0")
            tree.focus("0")
        try:
            win.lift()
            win.focus_set()
        except Exception:
            pass

    def copy_handshake_string(self):
        """Copia negli appunti il riferimento al PCAP che contiene il 4-way handshake."""
        # Copia ESATTAMENTE il testo rappresentato a schermo nel riquadro HANDSHAKE.
        value=(self.handshake_state.get() or "").strip()
        if not value:
            self.set_status("Nessun PCAP con handshake completo da copiare.")
            self._set_handshake_copy_enabled(False)
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(value)
            self.root.update_idletasks()
            self.set_status("Handshake visualizzato copiato negli appunti.")
        except Exception as e:
            self.logmsg(f"Copia handshake fallita: {e}")


    def update_ap_client_count_display(self, bssid, count, band="?", replace=False):
        bssid=(bssid or "").lower()
        try:
            count=int(count)
        except Exception:
            count=0

        # Per default conserva il valore più alto già osservato tra scansione
        # client airodump e analisi PCAP. "replace=True" resta disponibile
        # se in futuro si vuole forzare un nuovo valore.
        previous = self.ap_client_counts.get(bssid, 0)
        try:
            previous = int(previous)
        except Exception:
            previous = 0
        displayed_count = count if replace else max(previous, count)
        self.ap_client_counts[bssid]=displayed_count

        if not hasattr(self, "ap_tree"):
            return

        cols=list(self.ap_tree["columns"])
        try:
            bi=cols.index("band")
            ci=cols.index("clients")
        except ValueError:
            return

        for item in self.ap_tree.get_children():
            vals=list(self.ap_tree.item(item,"values"))
            if len(vals) < 2 or str(vals[0]).lower()!=bssid:
                continue

            while len(vals) < len(cols):
                vals.append("")

            ch = vals[1] if len(vals) > 1 else ""
            detected_band = band if band!="?" else self.band_from_channel(ch)
            vals[bi]=detected_band
            vals[ci]=displayed_count
            self.ap_tree.item(item, values=vals)

    def band_from_channel(self, channel):
        try:
            ch=int(float(str(channel).strip()))
        except Exception:
            return "?"
        if 1 <= ch <= 14:
            return "2.4 GHz"
        if 32 <= ch <= 177:
            return "5 GHz"
        return "?"

    def clients_from_analysis_rows(self, rows):
        """Restituisce i MAC classificati come Wi-Fi ASSOCIATO dall'analisi già eseguita."""
        return {
            row[0].lower()
            for row in rows
            if len(row) >= 3 and row[2] == "Wi-Fi ASSOCIATO"
        }

    def count_associated_clients_for_bssid(self, cap, bssid):
        """
        Conta passivamente le station Wi-Fi osservate sull'AP selezionato.
        Usa DATA ToDS/FromDS come evidenza principale e aggiunge EAPOL/
        association/reassociation/authentication come evidenza radio.
        """
        bssid=(bssid or "").lower()
        cmd=[
            "tshark","-r",str(cap),"-T","fields",
            "-E","separator=/t","-E","occurrence=f",
            "-e","wlan.fc.type",
            "-e","wlan.fc.type_subtype",
            "-e","wlan.fc.tods",
            "-e","wlan.fc.fromds",
            "-e","wlan.ta",
            "-e","wlan.ra",
            "-e","wlan.sa",
            "-e","wlan.da",
            "-e","wlan.bssid",
            "-e","eapol.type"
        ]
        p=run(cmd, timeout=20)
        if p.returncode != 0:
            self.logmsg("Conteggio client tshark fallito: " + (p.stderr or "errore sconosciuto"))
            return set()

        def norm_mac(v):
            m=MAC_FIND.search(v or "")
            return m.group(0).lower() if m else ""

        def num_field(v):
            s=(v or "").strip().lower()
            if not s:
                return None
            try:
                return int(s, 0)
            except Exception:
                try:
                    return int(float(s))
                except Exception:
                    return None

        clients=set()

        for line in p.stdout.splitlines():
            f=line.split("\t")
            f += [""]*(10-len(f))
            ftype,subtype,tods,fromds,ta,ra,sa,da,fbssid,eapol_type=f[:10]

            typ=num_field(ftype)
            sub=num_field(subtype)
            to_ds=num_field(tods)==1
            from_ds=num_field(fromds)==1

            ta=norm_mac(ta)
            ra=norm_mac(ra)
            sa=norm_mac(sa)
            da=norm_mac(da)
            fbssid=norm_mac(fbssid)

            # Il frame appartiene all'AP se il BSSID esplicito coincide,
            # oppure se l'AP compare come trasmettitore/ricevitore radio.
            belongs = (
                fbssid == bssid
                or ta == bssid
                or ra == bssid
            )
            if not belongs:
                continue

            station=""

            # DATA frame infrastruttura.
            if typ == 2:
                if to_ds and not from_ds:
                    # STA -> AP
                    if ra == bssid or fbssid == bssid:
                        station = ta or sa
                elif from_ds and not to_ds:
                    # AP -> STA
                    if ta == bssid or fbssid == bssid:
                        station = ra or da

            # Management frame che provano presenza radio del client.
            # 0 assoc req, 2 reassoc req, 11 authentication.
            elif typ == 0 and sub in (0, 2, 11):
                if ta != bssid:
                    station = ta or sa
                elif ra != bssid:
                    station = ra or da

            # EAPOL visto tra AP e station.
            if not station and (eapol_type or "").strip():
                for cand in (ta,ra,sa,da):
                    if cand and cand != bssid:
                        station=cand
                        break

            if (
                station
                and station != bssid
                and MAC_FULL.match(station)
                and not self.is_multicast_or_broadcast(station)
            ):
                clients.add(station)

        self.logmsg(
            f"Client Wi-Fi osservati per {bssid}: {len(clients)}"
            + (f" -> {', '.join(sorted(clients))}" if clients else "")
        )
        return clients

    def _raw_80211_global_radio_stations(self, cap):
        """Return MACs directly observed as 802.11 stations on ANY BSSID.

        This is deliberately independent from the selected BSSID.  A client connected
        to another SSID/BSSID/band of the same router may appear behind Address3 in
        traffic of the monitored BSSID and look like a wired LAN endpoint.  If the
        same MAC is directly seen as a radio station anywhere in the PCAP, radio
        evidence wins and the MAC must be excluded from the LAN table.
        """
        stations = set()
        path = Path(cap)
        if not path.exists():
            return stations

        def mac_at(buf, off):
            if off < 0 or off + 6 > len(buf):
                return ""
            return ":".join(f"{x:02x}" for x in buf[off:off+6])

        def add(mac):
            if (
                mac
                and MAC_FULL.match(mac)
                and mac != "00:00:00:00:00:00"
                and not self.is_multicast_or_broadcast(mac)
            ):
                stations.add(mac)

        try:
            raw = path.read_bytes()
        except Exception:
            return stations

        if len(raw) < 24:
            return stations

        magic = raw[:4]
        if magic in (b"\xd4\xc3\xb2\xa1", b"\x4d\x3c\xb2\xa1"):
            endian = "<"
        elif magic in (b"\xa1\xb2\xc3\xd4", b"\xa1\xb2\x3c\x4d"):
            endian = ">"
        else:
            return stations

        try:
            _magic, _maj, _min, _tz, _sig, _snaplen, linktype = struct.unpack(
                endian + "IHHIIII", raw[:24]
            )
        except Exception:
            return stations

        if linktype not in (105, 127):
            return stations

        pos = 24
        while pos + 16 <= len(raw):
            try:
                ts_sec, ts_frac, incl_len, orig_len = struct.unpack_from(
                    endian + "IIII", raw, pos
                )
            except Exception:
                break
            pos += 16
            if incl_len < 0 or pos + incl_len > len(raw):
                break

            pkt = raw[pos:pos+incl_len]
            pos += incl_len

            dot11 = pkt
            if linktype == 127:
                if len(pkt) < 8:
                    continue
                try:
                    rt_len = struct.unpack_from("<H", pkt, 2)[0]
                except Exception:
                    continue
                if rt_len < 8 or rt_len >= len(pkt):
                    continue
                dot11 = pkt[rt_len:]

            if len(dot11) < 24:
                continue

            try:
                fc = struct.unpack_from("<H", dot11, 0)[0]
            except Exception:
                continue

            ftype = (fc >> 2) & 0x3
            subtype = (fc >> 4) & 0xF
            to_ds = bool((fc >> 8) & 1)
            from_ds = bool((fc >> 9) & 1)

            a1 = mac_at(dot11, 4)
            a2 = mac_at(dot11, 10)

            if ftype == 2:
                # STA -> AP: transmitter (Address2) is the station.
                if to_ds and not from_ds:
                    add(a2)
                # AP -> STA: receiver (Address1) is the station.
                elif from_ds and not to_ds:
                    add(a1)

            elif ftype == 0:
                # Association/Reassociation request, Probe request and Authentication
                # are strong direct-radio evidence from a station.
                if subtype in (0, 2, 4, 11):
                    add(a2)

        return stations


    def _known_ap_bssids(self):
        """Restituisce i BSSID noti dell'infrastruttura Wi-Fi.

        Un BSSID/AP non deve mai essere promosso a dispositivo LAN o telecamera.
        """
        out=set()
        try:
            cur=str(self._dual_band_value(getattr(self,"bssid","")) or "").strip().lower()
            if MAC_FULL.match(cur):
                out.add(cur)
        except Exception:
            try:
                cur=str(getattr(self,"bssid",tk.StringVar()).get() or "").strip().lower()
                if MAC_FULL.match(cur):
                    out.add(cur)
            except Exception:
                pass
        try:
            for iid in self.ap_tree.get_children(""):
                vals=tuple(self.ap_tree.item(iid,"values") or ())
                if not vals:
                    continue
                m=str(vals[0] or "").strip().lower()
                if MAC_FULL.match(m):
                    out.add(m)
        except Exception:
            pass
        try:
            for vals in (getattr(self,"_dual_band_ap_snapshot",{}) or {}).values():
                vals=tuple(vals or ())
                if not vals:
                    continue
                m=str(vals[0] or "").strip().lower()
                if MAC_FULL.match(m):
                    out.add(m)
        except Exception:
            pass
        try:
            m=str(getattr(self,"_cascade_second_scan_target_bssid","") or "").strip().lower()
            if MAC_FULL.match(m):
                out.add(m)
        except Exception:
            pass

        # La scansione router visibile puo' cambiare durante la sessione. Per le
        # esclusioni camera/NVR bisogna ricordare anche tutti i BSSID gia' visti.
        try:
            _hist = getattr(self, "_network_graph_history", {}) or {}
            for _m in ((_hist.get("routers", {}) or {}).keys()):
                _m = str(_m or "").strip().lower()
                if MAC_FULL.match(_m):
                    out.add(_m)
        except Exception:
            pass
        try:
            for _rel in (getattr(self, "_network_graph_relations", []) or []):
                for _k in ("parent", "child", "a", "b"):
                    _m = str(_rel.get(_k, "") or "").strip().lower()
                    if MAC_FULL.match(_m):
                        out.add(_m)
        except Exception:
            pass
        return out



    def _is_camera_infrastructure_mac(self, mac, vendor=""):
        """True se il MAC appartiene con alta probabilita' a router/AP/infrastruttura.

        Safety-net comune a camera Wi-Fi, camera LAN e NVR. Oltre al BSSID
        esatto, riconosce le interfacce LAN/WAN radio dello stesso apparato
        quando il MAC e' adiacente a un BSSID noto. Questo evita che il bridge
        interno di un router venga scambiato per un NVR solo perche' riceve molto
        traffico ToDS/FromDS.
        """
        m = str(mac or "").replace("(*)", "").strip().lower()
        if not MAC_FULL.match(m):
            return False
        aps = set(self._known_ap_bssids())
        try:
            cur = str(self._dual_band_value(getattr(self, "bssid", "")) or "").strip().lower()
            if MAC_FULL.match(cur):
                aps.add(cur)
        except Exception:
            pass
        if m in aps:
            return True

        def _parts(x):
            return str(x or "").lower().split(":")

        def _adjacent_router_interface(a, b):
            """Firma forte di due interfacce dello stesso apparato."""
            pa, pb = _parts(a), _parts(b)
            if len(pa) != 6 or len(pb) != 6:
                return False
            try:
                la, lb = int(pa[5], 16), int(pb[5], 16)
                # Caso piu' forte: primi 5 ottetti uguali, ultimo quasi consecutivo.
                if pa[:5] == pb[:5] and abs(la - lb) <= 16:
                    return True
                # Alcuni router alternano il bit U/L del primo ottetto fra radio,
                # bridge, WAN e LAN. Gli altri quattro ottetti centrali restano uguali.
                fa, fb = int(pa[0], 16), int(pb[0], 16)
                ul_compatible = ((fa ^ fb) in (0x00, 0x02))
                if ul_compatible and pa[1:5] == pb[1:5] and abs(la - lb) <= 32:
                    return True
            except Exception:
                return False
            return False

        # Una relazione MAC quasi consecutiva con un BSSID noto e' gia' una
        # prova infrastrutturale forte e non richiede che il database OUI sia aggiornato.
        for ap in aps:
            if _adjacent_router_interface(m, ap):
                return True

        # Fallback vendor: richiede comunque la vicinanza a un BSSID noto.
        v = str(vendor or "").lower()
        router_words = (
            "zte", "vodafone", "technicolor", "vantiva", "thomson",
            "sagemcom", "sercomm", "arcadyan", "router", "gateway",
            "access point", "tp-link", "tplink", "netgear", "d-link",
            "dlink", "asus", "zyxel", "mikrotik", "ubiquiti",
            "mercusys", "tenda", "linksys", "huawei"
        )
        if not any(w in v for w in router_words):
            return False
        try:
            mi = int(m.replace(":", ""), 16)
        except Exception:
            return False
        for ap in aps:
            try:
                api = int(ap.replace(":", ""), 16)
                # OUI identico e distanza stretta: interfaccia dello stesso CPE.
                if m[:8] == ap[:8] and abs(mi - api) <= 64:
                    return True
            except Exception:
                pass
        return False


    def _related_radio_bssids(self, bssid):
        """BSSID di radio sorelle: confronto sui 4 byte centrali, come il controllo dual-band."""
        b=str(bssid or "").strip().lower()
        if not MAC_FULL.match(b):
            return set()
        parts=b.split(":")
        key=tuple(parts[1:-1])
        out=set()
        candidates=[]
        try:
            for iid in self.ap_tree.get_children(""):
                vals=tuple(self.ap_tree.item(iid,"values") or ())
                if vals:
                    candidates.append(str(vals[0]).strip().lower())
        except Exception:
            pass
        try:
            for vals in (getattr(self,"_dual_band_ap_snapshot",{}) or {}).values():
                vals=tuple(vals or ())
                if vals:
                    candidates.append(str(vals[0]).strip().lower())
        except Exception:
            pass
        for m in candidates:
            if not MAC_FULL.match(m) or m==b:
                continue
            p=m.split(":")
            if tuple(p[1:-1])==key:
                out.add(m)
        return out

    def _raw_80211_lan_candidates(self, cap, bssid):
        """
        Fallback LAN indipendente da tshark.

        Legge direttamente gli header MAC IEEE 802.11 dal PCAP senza decifrare
        il payload. Questo è sufficiente per ricavare Address1/2/3/4 e i bit
        ToDS/FromDS, che restano visibili anche su reti WPA/WPA2 cifrate.

        Supporta PCAP classico con linktype:
          105 = IEEE802_11
          127 = IEEE802_11_RADIOTAP

        Restituisce:
            {mac: {"fromds":N, "tods":N, "wds_src":N, "wds_dst":N,
                   "first":ts, "last":ts, "bytes":N}}
        """
        result = {}
        path = Path(cap)
        if not path.exists():
            return result

        bssid = (bssid or "").strip().lower()
        if not MAC_FULL.match(bssid):
            return result

        def mac_at(buf, off):
            if off < 0 or off + 6 > len(buf):
                return ""
            return ":".join(f"{x:02x}" for x in buf[off:off+6])

        def valid_endpoint(mac, *exclude):
            if not mac or mac in ("00:00:00:00:00:00", bssid):
                return False
            if mac in exclude:
                return False
            return MAC_FULL.match(mac) and not self.is_multicast_or_broadcast(mac)

        def note(mac, kind, ts, size):
            rec = result.setdefault(mac, {
                "fromds":0, "tods":0, "wds_src":0, "wds_dst":0,
                "first":None, "last":None, "bytes":0
            })
            rec[kind] = int(rec.get(kind, 0)) + 1
            try:
                ts = float(ts)
                rec["first"] = ts if rec["first"] is None else min(rec["first"], ts)
                rec["last"] = ts if rec["last"] is None else max(rec["last"], ts)
            except Exception:
                pass
            rec["bytes"] += max(0, int(size or 0))

        try:
            raw = path.read_bytes()
        except Exception as e:
            self.logmsg(f"LAN RAW: impossibile leggere PCAP: {e}")
            return result

        if len(raw) < 24:
            return result

        magic = raw[:4]
        if magic in (b"\xd4\xc3\xb2\xa1", b"\x4d\x3c\xb2\xa1"):
            endian = "<"
        elif magic in (b"\xa1\xb2\xc3\xd4", b"\xa1\xb2\x3c\x4d"):
            endian = ">"
        else:
            # PCAPNG o formato non supportato dal fallback raw.
            self.logmsg("LAN RAW: formato non-PCAP classico; uso solo tshark.")
            return result

        try:
            _magic, _maj, _min, _tz, _sig, _snaplen, linktype = struct.unpack(
                endian + "IHHIIII", raw[:24]
            )
        except Exception:
            return result

        if linktype not in (105, 127):
            self.logmsg(f"LAN RAW: linktype {linktype} non gestito dal fallback.")
            return result

        pos = 24
        packet_count = 0
        while pos + 16 <= len(raw):
            try:
                ts_sec, ts_frac, incl_len, orig_len = struct.unpack_from(
                    endian + "IIII", raw, pos
                )
            except Exception:
                break
            pos += 16

            if incl_len < 0 or pos + incl_len > len(raw):
                break

            pkt = raw[pos:pos+incl_len]
            pos += incl_len
            packet_count += 1

            # Salta Radiotap se presente.
            dot11 = pkt
            if linktype == 127:
                if len(pkt) < 8:
                    continue
                try:
                    rt_len = struct.unpack_from("<H", pkt, 2)[0]
                except Exception:
                    continue
                if rt_len < 8 or rt_len >= len(pkt):
                    continue
                dot11 = pkt[rt_len:]

            if len(dot11) < 24:
                continue

            try:
                fc = struct.unpack_from("<H", dot11, 0)[0]
            except Exception:
                continue

            ftype = (fc >> 2) & 0x3
            to_ds = bool((fc >> 8) & 1)
            from_ds = bool((fc >> 9) & 1)

            # Solo DATA: ACK/control, probe e management non sono prova LAN.
            if ftype != 2:
                continue

            a1 = mac_at(dot11, 4)
            a2 = mac_at(dot11, 10)
            a3 = mac_at(dot11, 16)
            a4 = mac_at(dot11, 24) if (to_ds and from_ds and len(dot11) >= 30) else ""

            ts = float(ts_sec) + float(ts_frac) / 1000000.0

            if to_ds and not from_ds:
                # STA -> AP: Address1=BSSID, Address2=STA, Address3=dest finale DS
                if a1 != bssid:
                    continue
                sta = a2
                if valid_endpoint(a3, sta):
                    note(a3, "tods", ts, orig_len)

            elif from_ds and not to_ds:
                # AP -> STA: Address2=BSSID, Address1=STA, Address3=sorgente finale DS
                if a2 != bssid:
                    continue
                sta = a1
                if valid_endpoint(a3, sta):
                    note(a3, "fromds", ts, orig_len)

            elif to_ds and from_ds:
                # WDS: non esiste un BSSID tradizionale. Consideriamo il frame
                # solo se il BSSID selezionato coincide con RA o TA.
                if bssid not in (a1, a2):
                    continue
                if valid_endpoint(a4, a1, a2, a3):
                    note(a4, "wds_src", ts, orig_len)
                if valid_endpoint(a3, a1, a2, a4):
                    note(a3, "wds_dst", ts, orig_len)

        if result:
            summary = ", ".join(
                f"{mac}[F={r['fromds']},T={r['tods']},WS={r['wds_src']},WD={r['wds_dst']}]"
                for mac, r in sorted(
                    result.items(),
                    key=lambda kv: -sum(
                        int(kv[1].get(k,0)) for k in ("fromds","tods","wds_src","wds_dst")
                    )
                )[:20]
            )
            self.logmsg(f"LAN RAW: {len(result)} endpoint DS trovati su {packet_count} frame: {summary}")
        else:
            self.logmsg(f"LAN RAW: nessun endpoint DS trovato su {packet_count} frame.")

        return result

    def analyze(self,cap,bssid,client):
        is_en = getattr(self,"language","it") == "en"
        bssid = bssid.lower()
        zero = "00:00:00:00:00:00"

        # Analisi LAN basata sulla semantica IEEE 802.11 ToDS/FromDS.
        #
        # FromDS=0 / ToDS=0:
        #   Address1=DA, Address2=SA, Address3=BSSID -> traffico non-DS/ad-hoc.
        #   NON viene usato come prova di dispositivo LAN.
        #
        # FromDS=0 / ToDS=1 (STA -> AP/DS):
        #   Address1=BSSID/RA, Address2=STA/TA-SA, Address3=destinazione finale.
        #   Address3 può quindi rivelare un endpoint lato LAN/Distribution System.
        #
        # FromDS=1 / ToDS=0 (AP/DS -> STA):
        #   Address1=STA/RA-DA, Address2=BSSID/TA, Address3=sorgente finale.
        #   Address3 può quindi rivelare un endpoint lato LAN/Distribution System.
        #
        # FromDS=1 / ToDS=1:
        #   frame WDS/bridge a quattro indirizzi:
        #   Addr1=Receiver, Addr2=Transmitter, Addr3=Destination, Addr4=Source.
        #   tshark espone normalmente Source/Destination logici come wlan.sa/wlan.da.
        #
        # ACK/Control e Probe Request non vengono mai usati come prova LAN.
        # Broadcast/multicast non vengono contati come dispositivi, ma una sorgente
        # unicast lato DS che invia un broadcast costituisce evidenza aggiuntiva.
        cmd=[
            "tshark","-r",str(cap),"-T","fields",
            "-E","separator=/t","-E","occurrence=f",
            "-e","wlan.fc.type","-e","wlan.fc.type_subtype",
            "-e","wlan.fc.tods","-e","wlan.fc.fromds",
            "-e","wlan.sa","-e","wlan.da","-e","wlan.ta","-e","wlan.ra",
            "-e","wlan.bssid","-e","eth.src","-e","eth.dst",
            "-e","arp.src.hw_mac","-e","arp.dst.hw_mac",
            "-e","eapol.type","-e","frame.time_epoch","-e","frame.len"
        ]
        p=run(cmd, timeout=15)
        if p.returncode != 0:
            # NON interrompere l'analisi LAN: il fallback RAW IEEE 802.11
            # funziona direttamente sul PCAP e non dipende da tshark.
            self.logmsg(
                "Analisi tshark parziale/non disponibile: "
                + (p.stderr or "errore sconosciuto")
                + " - continuo con parser RAW 802.11."
            )
            tshark_output = ""
        else:
            tshark_output = p.stdout or ""

        observed=set()
        wifi_assoc=set()
        wifi_radio_seen=set()
        lan_candidates=set()

        # Diagnostica di osservabilita' LAN/DS: misura se la cattura radio
        # contiene davvero traffico capace di esporre endpoint cablati.
        lan_obs = {
            "tods":0, "fromds":0, "wds":0,
            "addr3_unicast":0, "addr3_unique":set(),
            "ds_endpoint_hits":0, "broadcast_ds":0
        }

        # Contatori di evidenza per rendere la classificazione trasparente.
        ev = {}

        def note_ev(mac, kind):
            if kind in ("ds","sa_fromds","da_tods","wds_src","wds_dst"):
                lan_obs["ds_endpoint_hits"] += 1
            if not mac:
                return
            rec = ev.setdefault(mac, {
                "data":0,
                "eapol":0,
                "assoc":0,
                "auth":0,
                "ds":0,
                "sa_fromds":0,
                "da_tods":0,
                "wds_src":0,
                "wds_dst":0,
                "fromds_bcast":0,
                "wds_bcast":0,
                "eth_src":0,
                "eth_dst":0,
                "arp_src":0,
                "arp_dst":0,
                "neigh":0,
                "fdb":0,
                "first_ts":None,
                "last_ts":None,
                "bytes":0
            })
            if kind in rec:
                rec[kind] += 1

        def note_activity(mac, ts, flen):
            if not mac:
                return
            rec = ev.setdefault(mac, {
                "data":0,"eapol":0,"assoc":0,"auth":0,"ds":0,
                "sa_fromds":0,"da_tods":0,"wds_src":0,"wds_dst":0,
                "fromds_bcast":0,"wds_bcast":0,"eth_src":0,"eth_dst":0,
                "arp_src":0,"arp_dst":0,"neigh":0,"fdb":0,"first_ts":None,"last_ts":None,"bytes":0
            })
            try:
                t=float(ts)
                if t > 0:
                    rec["first_ts"] = t if rec["first_ts"] is None else min(rec["first_ts"], t)
                    rec["last_ts"] = t if rec["last_ts"] is None else max(rec["last_ts"], t)
                    # Bucket da 20 s: distingue attività realmente persistente
                    # da molti frame concentrati nello stesso breve burst.
                    rec.setdefault("_activity_bins20", set()).add(int(t // 20.0))
            except Exception:
                pass
            try:
                rec["bytes"] += max(0, int(float(flen or 0)))
            except Exception:
                pass

        def macs(value):
            return [m.lower() for m in MAC_FIND.findall(value or "")]

        def first_mac(value):
            vals=macs(value)
            return vals[0] if vals else ""

        for line in tshark_output.splitlines():
            fields=line.split("\t")
            fields += [""] * (16-len(fields))
            (ftype, subtype, tods, fromds, sa, da, ta, ra,
             frame_bssid, eth_src, eth_dst, arp_src, arp_dst,
             eapol_type, frame_ts, frame_len) = fields[:16]

            frame_macs=set()
            for value in (sa,da,ta,ra,frame_bssid,eth_src,eth_dst,arp_src,arp_dst):
                frame_macs.update(macs(value))
            frame_macs.discard(zero)
            observed.update(frame_macs)

            fb=first_mac(frame_bssid)
            ta_m=first_mac(ta)
            ra_m=first_mac(ra)

            # Alcuni driver/capture non valorizzano wlan.bssid in tutti i frame.
            # Considera appartenente all'AP anche un frame in cui il BSSID
            # compare come transmitter/receiver address.
            if fb != bssid and ta_m != bssid and ra_m != bssid:
                continue

            def _num(v):
                s=(v or "").strip().lower()
                try:
                    return int(s,0)
                except Exception:
                    try:
                        return int(float(s))
                    except Exception:
                        return None

            ftype_s=_num(ftype)
            subtype_s=_num(subtype)

            def _flag(v):
                s=(v or "").strip().lower()
                if s in ("1","true","yes","set"):
                    return True
                if s in ("0","false","no","not set",""):
                    return False
                n=_num(v)
                return bool(n) if n is not None else False

            to_ds=_flag(tods)
            from_ds=_flag(fromds)

            # --------------------------------------------------------------
            # FRAME DATA: interpreta i quattro casi ToDS/FromDS.
            # --------------------------------------------------------------
            if ftype_s == 2:
                sa_m = first_mac(sa)
                da_m = first_mac(da)

                # Osservabilità DS: un solo incremento per frame DATA.
                if to_ds and from_ds:
                    lan_obs["wds"] += 1
                elif to_ds:
                    lan_obs["tods"] += 1
                elif from_ds:
                    lan_obs["fromds"] += 1

                if not from_ds and not to_ds:
                    # 0/0: non attraversa il Distribution System.
                    # Non inferiamo alcun host LAN da questo caso.
                    pass

                elif to_ds and not from_ds:
                    # 0/1: STA -> AP/DS
                    # Addr2 / TA = station Wi-Fi.
                    station = ta_m or sa_m
                    if (
                        station
                        and station not in (bssid, zero)
                        and not self.is_multicast_or_broadcast(station)
                    ):
                        wifi_assoc.add(station)
                        wifi_radio_seen.add(station)
                        note_ev(station, "data")
                        note_activity(station, frame_ts, frame_len)

                    # Addr3 = destinazione finale nel DS.
                    # Se unicast e non è la station/AP, è un candidato LAN/DS.
                    dest_addr = da_m
                    if (
                        dest_addr
                        and dest_addr not in (bssid, zero, station)
                        and not self.is_multicast_or_broadcast(dest_addr)
                    ):
                        lan_candidates.add(dest_addr)
                        note_ev(dest_addr, "ds")
                        note_ev(dest_addr, "da_tods")
                        note_activity(dest_addr, frame_ts, frame_len)

                        if dest_addr in macs(eth_dst):
                            note_ev(dest_addr, "eth_dst")
                        if dest_addr in macs(arp_dst):
                            note_ev(dest_addr, "arp_dst")

                elif from_ds and not to_ds:
                    # 1/0: AP/DS -> STA
                    # Addr1 / RA = station Wi-Fi destinataria quando unicast.
                    station = ra_m or da_m
                    if (
                        station
                        and station not in (bssid, zero)
                        and not self.is_multicast_or_broadcast(station)
                    ):
                        wifi_assoc.add(station)
                        wifi_radio_seen.add(station)
                        note_ev(station, "data")
                        note_activity(station, frame_ts, frame_len)

                    # Addr3 = sorgente finale nel Distribution System.
                    source_addr = sa_m
                    if (
                        source_addr
                        and source_addr not in (bssid, zero, station)
                        and not self.is_multicast_or_broadcast(source_addr)
                    ):
                        lan_candidates.add(source_addr)
                        note_ev(source_addr, "ds")
                        note_ev(source_addr, "sa_fromds")
                        note_activity(source_addr, frame_ts, frame_len)

                        if source_addr in macs(eth_src):
                            note_ev(source_addr, "eth_src")
                        if source_addr in macs(arp_src):
                            note_ev(source_addr, "arp_src")

                        # Se il frame proveniente dal DS è diretto a broadcast/
                        # multicast, la sorgente unicast resta un endpoint reale
                        # lato DS e il broadcast rafforza l'evidenza.
                        if da_m and self.is_multicast_or_broadcast(da_m):
                            note_ev(source_addr, "fromds_bcast")

                elif from_ds and to_ds:
                    # 1/1: WDS / bridge a 4 indirizzi.
                    # wlan.sa = Source logica (Addr4), wlan.da = Destination logica
                    # (Addr3) nelle normali dissezioni tshark.
                    source_addr = sa_m
                    dest_addr = da_m

                    if (
                        source_addr
                        and source_addr not in (bssid, zero, ta_m, ra_m)
                        and not self.is_multicast_or_broadcast(source_addr)
                    ):
                        lan_candidates.add(source_addr)
                        note_ev(source_addr, "ds")
                        note_ev(source_addr, "wds_src")
                        note_activity(source_addr, frame_ts, frame_len)
                        if source_addr in macs(eth_src):
                            note_ev(source_addr, "eth_src")
                        if source_addr in macs(arp_src):
                            note_ev(source_addr, "arp_src")
                        if dest_addr and self.is_multicast_or_broadcast(dest_addr):
                            note_ev(source_addr, "wds_bcast")

                    if (
                        dest_addr
                        and dest_addr not in (bssid, zero, ta_m, ra_m, source_addr)
                        and not self.is_multicast_or_broadcast(dest_addr)
                    ):
                        lan_candidates.add(dest_addr)
                        note_ev(dest_addr, "ds")
                        note_ev(dest_addr, "wds_dst")
                        note_activity(dest_addr, frame_ts, frame_len)
                        if dest_addr in macs(eth_dst):
                            note_ev(dest_addr, "eth_dst")
                        if dest_addr in macs(arp_dst):
                            note_ev(dest_addr, "arp_dst")

            # EAPOL: traffico radio di autenticazione WPA/WPA2.
            if eapol_type.strip():
                for cand in (first_mac(sa), first_mac(da), first_mac(ta), first_mac(ra)):
                    if cand and cand not in (bssid,zero) and not self.is_multicast_or_broadcast(cand):
                        wifi_radio_seen.add(cand)
                        note_ev(cand, "eapol")

            # Management frame utili per vedere client che tentano/effettuano associazione.
            # 0x00 assoc req, 0x02 reassoc req, 0x0b auth.
            if ftype_s == 0:
                candidate = ""
                if subtype_s == 0:
                    candidate = first_mac(sa) or first_mac(ta)
                    if candidate and candidate not in (bssid,zero) and not self.is_multicast_or_broadcast(candidate):
                        wifi_radio_seen.add(candidate)
                        note_ev(candidate, "assoc")
                elif subtype_s == 2:
                    candidate = first_mac(sa) or first_mac(ta)
                    if candidate and candidate not in (bssid,zero) and not self.is_multicast_or_broadcast(candidate):
                        wifi_radio_seen.add(candidate)
                        note_ev(candidate, "assoc")
                elif subtype_s == 11:
                    candidate = first_mac(sa) or first_mac(ta)
                    if candidate and candidate not in (bssid,zero) and not self.is_multicast_or_broadcast(candidate):
                        wifi_radio_seen.add(candidate)
                        note_ev(candidate, "auth")

        # ------------------------------------------------------------------
        # NOTA IMPORTANTE SULLE FONTI LOCALI
        # ------------------------------------------------------------------
        # Non usiamo "ip neigh" o "bridge fdb show" del computer che esegue
        # wifi_400 come prova di dispositivi LAN del router monitorato: quelle
        # tabelle descrivono la rete locale DEL COMPUTER e possono non coincidere
        # con il Distribution System dell'AP sniffato. Per evitare falsi positivi,
        # la classificazione LAN qui sotto usa solo evidenze appartenenti al BSSID
        # selezionato e realmente presenti nel PCAP.
        #
        # Un host Ethernet può essere osservato via radio soltanto quando il suo
        # traffico viene inoltrato dall'AP verso/da una station Wi-Fi durante la
        # cattura. Se non attraversa la radio, il PCAP 802.11 non può rivelarlo.
        # ------------------------------------------------------------------

        # --------------------------------------------------------------
        # FALLBACK RAW 802.11
        # --------------------------------------------------------------
        # Non dipende dalla decodifica del payload né dalla password Wi-Fi.
        # Se tshark non espone correttamente wlan.sa/wlan.da o i booleani DS,
        # leggiamo direttamente Address1/2/3/4 dall'header MAC del PCAP.
        try:
            raw_lan = self._raw_80211_lan_candidates(cap, bssid)
        except Exception as e:
            self.logmsg(f"LAN RAW: errore fallback: {e}")
            raw_lan = {}

        # Rileva eventuali radio/BSSID "sorelle" dello stesso router.
        # Esempio tipico: BSSID selezionato ...:B7 e altra radio ...:B6.
        # Se una radio sorella è presente, i suoi client Wi-Fi possono apparire
        # in Address3 come endpoint DS e sembrare falsamente dispositivi Ethernet.
        bridge_sibling_radios = set()
        try:
            _bp = bssid.split(":")
            _bprefix = ":".join(_bp[:5])
            _blast = int(_bp[5], 16)
            for _m, _r in raw_lan.items():
                _mp = str(_m).lower().split(":")
                if len(_mp) != 6 or ":".join(_mp[:5]) != _bprefix:
                    continue
                try:
                    _mlast = int(_mp[5], 16)
                except Exception:
                    continue
                _hits = sum(int(_r.get(k, 0)) for k in ("fromds","tods","wds_src","wds_dst"))
                if 0 < abs(_mlast - _blast) <= 4 and _hits >= 20:
                    bridge_sibling_radios.add(str(_m).lower())
        except Exception:
            bridge_sibling_radios = set()

        if bridge_sibling_radios:
            self.logmsg(
                (
                    "Detected sibling Wi-Fi radio(s) of the router: "
                    if is_en else
                    "Rilevate radio Wi-Fi sorelle del router: "
                )
                + ", ".join(sorted(bridge_sibling_radios))
            )

        infrastructure_bssids = set(self._known_ap_bssids())
        infrastructure_bssids.add(bssid)

        for raw_mac, raw_rec in raw_lan.items():
            if not MAC_FULL.match(raw_mac) or self.is_multicast_or_broadcast(raw_mac):
                continue
            if raw_mac in infrastructure_bssids:
                # Un BSSID/AP noto e' infrastruttura radio, non host LAN.
                continue
            if raw_mac in bridge_sibling_radios:
                # Interfaccia/radio del router, non dispositivo Ethernet.
                continue

            lan_candidates.add(raw_mac)
            observed.add(raw_mac)

            rec = ev.setdefault(raw_mac, {
                "data":0,"eapol":0,"assoc":0,"auth":0,"ds":0,
                "sa_fromds":0,"da_tods":0,"wds_src":0,"wds_dst":0,
                "fromds_bcast":0,"wds_bcast":0,"eth_src":0,"eth_dst":0,
                "arp_src":0,"arp_dst":0,"neigh":0,"fdb":0,
                "first_ts":None,"last_ts":None,"bytes":0
            })

            rf = int(raw_rec.get("fromds",0))
            rt = int(raw_rec.get("tods",0))
            rws = int(raw_rec.get("wds_src",0))
            rwd = int(raw_rec.get("wds_dst",0))

            # Usiamo il massimo, non la somma, per evitare di contare due volte
            # gli stessi frame già riconosciuti anche da tshark.
            rec["sa_fromds"] = max(int(rec.get("sa_fromds",0)), rf)
            rec["da_tods"] = max(int(rec.get("da_tods",0)), rt)
            rec["wds_src"] = max(int(rec.get("wds_src",0)), rws)
            rec["wds_dst"] = max(int(rec.get("wds_dst",0)), rwd)
            rec["ds"] = max(
                int(rec.get("ds",0)),
                rf + rt + rws + rwd
            )

            rfirst = raw_rec.get("first")
            rlast = raw_rec.get("last")
            if rfirst is not None:
                rec["first_ts"] = (
                    float(rfirst) if rec.get("first_ts") is None
                    else min(float(rec["first_ts"]), float(rfirst))
                )
            if rlast is not None:
                rec["last_ts"] = (
                    float(rlast) if rec.get("last_ts") is None
                    else max(float(rec["last_ts"]), float(rlast))
                )
            rec["bytes"] = max(int(rec.get("bytes",0)), int(raw_rec.get("bytes",0)))

        # Cerca anche station radio appartenenti ad ALTRI BSSID/SSID/bande presenti
        # nel PCAP. Questo è fondamentale sui modem dual-band/mesh: un client Wi-Fi
        # di un'altra radio può comparire come Address3 dietro il BSSID selezionato.
        try:
            global_radio_seen = self._raw_80211_global_radio_stations(cap)
        except Exception:
            global_radio_seen = set()

        # Una station vista direttamente via radio prevale SEMPRE su una comparsa
        # come endpoint Address3/Address4 lato Distribution System o su una discovery IP locale.
        # Manteniamo la prova per tutta la sessione: se un MAC è stato visto come TA/SA/RA
        # di una station Wi-Fi del BSSID, non potrà più ricomparire come dispositivo LAN.
        if not isinstance(getattr(self, "wifi_radio_macs_session", None), set):
            self.wifi_radio_macs_session = set()
        self.wifi_radio_macs_session.update(wifi_radio_seen)
        self.wifi_radio_macs_session.update(wifi_assoc)
        self.wifi_radio_macs_session.update(global_radio_seen)
        self.wifi_radio_macs_session.discard(bssid)

        # Radio/BSSID sorelle dello stesso apparato non sono dispositivi LAN.
        # In una rete dual-band/mesh possono comparire in Address3 e generare
        # centinaia di frame DS, ma restano infrastruttura Wi-Fi.
        related_radio_bssids=self._related_radio_bssids(bssid)
        self.wifi_radio_macs_session.update(related_radio_bssids)
        if not isinstance(getattr(self,"wifi_radio_macs_global",None),set):
            self.wifi_radio_macs_global=set()
        self.wifi_radio_macs_global.update(self.wifi_radio_macs_session)

        lan_candidates.difference_update(self.wifi_radio_macs_session)
        lan_candidates.difference_update(infrastructure_bssids)

        # IMPORTANTE - RETE DUAL-BAND / CASCATA:
        # La presenza di una radio sorella 2.4/5 GHz NON deve cancellare in blocco
        # gli endpoint Address3/Address4 lato DS.
        #
        # Il vecchio filtro eliminava tutti gli endpoint solo-DS quando nel PCAP
        # compariva anche l'altra banda dello stesso router. Questo faceva sparire
        # dispositivi reali a valle (router/AP cablati, TV, bridge, ecc.).
        #
        # Adesso la regola è:
        #   - se il MAC è visto DIRETTAMENTE come station Wi-Fi su qualunque BSSID,
        #     la prova radio prevale ed è già stato escluso sopra;
        #   - se NON è mai visto come station radio, resta candidato LAN/DS;
        #   - la presenza della radio sorella viene conservata solo come fattore
        #     di ambiguità/confidenza, NON come esclusione assoluta.
        if related_radio_bssids:
            self._lan_sibling_radio_ambiguous_macs = set(lan_candidates)
            if lan_candidates:
                self.logmsg(
                    ("LAN dual-band: DS-only endpoints retained at reduced confidence; "
                     "only MACs directly observed as Wi-Fi stations are excluded: "
                     if is_en else
                     "LAN dual-band: endpoint solo-DS mantenuti a confidenza ridotta; "
                     "vengono esclusi solo i MAC osservati direttamente come station Wi-Fi: ")
                    + ", ".join(sorted(lan_candidates))
                )
        else:
            self._lan_sibling_radio_ambiguous_macs = set()

        # Valutazione separata dell'OSSERVABILITA' della LAN.
        # Non inventa dispositivi: spiega se il PCAP contiene abbastanza traffico
        # DS da permettere, in linea di principio, di vedere host dietro l'AP.
        ds_radio_frames = int(lan_obs["tods"]) + int(lan_obs["fromds"]) + int(lan_obs["wds"])
        candidate_count = len(lan_candidates)
        endpoint_hits = sum(
            int(r.get("sa_fromds",0)) + int(r.get("da_tods",0)) +
            int(r.get("wds_src",0)) + int(r.get("wds_dst",0))
            for r in ev.values()
        )
        if candidate_count >= 1 and endpoint_hits >= 10:
            lan_visibility_score = 100
            lan_visibility = "GOOD" if is_en else "BUONA"
        elif candidate_count >= 1 and endpoint_hits >= 3:
            lan_visibility_score = 75
            lan_visibility = "SUFFICIENT" if is_en else "SUFFICIENTE"
        elif candidate_count >= 1:
            lan_visibility_score = 55
            lan_visibility = "LIMITED" if is_en else "LIMITATA"
        elif ds_radio_frames >= 50:
            lan_visibility_score = 35
            lan_visibility = "INSUFFICIENT" if is_en else "INSUFFICIENTE"
        elif ds_radio_frames >= 10:
            lan_visibility_score = 20
            lan_visibility = "INSUFFICIENT" if is_en else "INSUFFICIENTE"
        else:
            lan_visibility_score = 5
            lan_visibility = "VERY LOW" if is_en else "MOLTO BASSA"

        self.lan_observability = {
            "level":lan_visibility,
            "score":lan_visibility_score,
            "tods":int(lan_obs["tods"]),
            "fromds":int(lan_obs["fromds"]),
            "wds":int(lan_obs["wds"]),
            "ds_frames":ds_radio_frames,
            "endpoint_hits":endpoint_hits,
            "candidates":candidate_count,
        }
        self.logmsg(
            (f"LAN VISIBILITY: {lan_visibility} ({lan_visibility_score}/100) | "
             f"ToDS={lan_obs['tods']} FromDS={lan_obs['fromds']} WDS={lan_obs['wds']} "
             f"DS-endpoint hits={endpoint_hits} candidates={candidate_count}")
            if is_en else
            (f"VISIBILITA' LAN: {lan_visibility} ({lan_visibility_score}/100) | "
             f"ToDS={lan_obs['tods']} FromDS={lan_obs['fromds']} WDS={lan_obs['wds']} "
             f"hit endpoint-DS={endpoint_hits} candidati={candidate_count}")
        )
        if candidate_count == 0:
            self.logmsg(
                ("No LAN device can be inferred from this capture. This does not prove that "
                 "the router has no wired devices: their traffic may simply never have crossed the Wi-Fi radio.")
                if is_en else
                ("Nessun dispositivo LAN deducibile da questa cattura. Questo NON dimostra che "
                 "il router non abbia dispositivi cablati: il loro traffico potrebbe non essere mai transitato sulla radio Wi-Fi.")
            )

        observed.add(bssid)
        observed.update(wifi_assoc)
        observed.update(wifi_radio_seen)
        observed.update(lan_candidates)

        cache=load_vendor_cache()
        out=[]
        for mac in sorted(observed):
            if mac == zero:
                continue

            rec = ev.get(mac, {
                "data":0,"eapol":0,"assoc":0,"auth":0,"ds":0,
                "sa_fromds":0,"da_tods":0,"wds_src":0,"wds_dst":0,
                "fromds_bcast":0,"wds_bcast":0,"eth_src":0,"eth_dst":0,
                "arp_src":0,"arp_dst":0,"neigh":0,"fdb":0,"first_ts":None,"last_ts":None,"bytes":0
            })

            if mac == bssid:
                cls="AP"
                evidence=("Selected BSSID" if is_en else "BSSID selezionato")
                notes=("Router/access point being captured" if is_en else "Router/access point oggetto della cattura")

            elif self.is_multicast_or_broadcast(mac):
                cls="MULTICAST/BROADCAST"
                evidence=("Group/service address" if is_en else "Indirizzo gruppo/servizio")
                notes=("Not counted as a device" if is_en else "Non contato come dispositivo")

            elif mac in wifi_assoc:
                cls="Wi-Fi ASSOCIATO"
                parts=[]
                if rec["data"]: parts.append(f"DATA radio {rec['data']}")
                if rec["eapol"]: parts.append(f"EAPOL {rec['eapol']}")
                if rec["assoc"]: parts.append(f"ASSOC {rec['assoc']}")
                if rec["auth"]: parts.append(f"AUTH {rec['auth']}")
                evidence=", ".join(parts) or ("infrastructure radio frame" if is_en else "frame radio infrastruttura")
                notes=("HIGH confidence: MAC address observed directly as a Wi-Fi station of the access point" if is_en else "ALTA confidenza: MAC osservato direttamente come station Wi-Fi dell\'AP")

            elif mac in wifi_radio_seen:
                # È stato visto direttamente come terminale radio, ma senza frame DATA sufficienti
                # per affermare che stesse trasportando traffico associato nel campione.
                cls="ALTRO/INCERTO"
                parts=[]
                if rec["eapol"]: parts.append(f"EAPOL {rec['eapol']}")
                if rec["assoc"]: parts.append(f"ASSOC {rec['assoc']}")
                if rec["auth"]: parts.append(f"AUTH {rec['auth']}")
                evidence=", ".join(parts) or ("radio management traffic" if is_en else "management radio")
                notes=("POSSIBLE WI-FI CLIENT: station observed over the air; active association not confirmed by DATA frames" if is_en else "Wi-Fi PROBABILE: client visto via radio; associazione attiva non provata dai frame DATA")

            elif mac in lan_candidates:
                cls="LAN CANDIDATO"

                from_hits=int(rec.get("sa_fromds",0))
                to_hits=int(rec.get("da_tods",0))
                wds_src_hits=int(rec.get("wds_src",0))
                wds_dst_hits=int(rec.get("wds_dst",0))
                bcast_hits=int(rec.get("fromds_bcast",0))+int(rec.get("wds_bcast",0))
                eth_hits=int(rec.get("eth_src",0))+int(rec.get("eth_dst",0))
                arp_hits=int(rec.get("arp_src",0))+int(rec.get("arp_dst",0))
                neigh_hits=int(rec.get("neigh",0))
                fdb_hits=int(rec.get("fdb",0))
                ds_hits=from_hits+to_hits+wds_src_hits+wds_dst_hits

                # Bidirezionalità classica STA<->DS oppure coppia source/dest WDS.
                bidirectional = (
                    (from_hits > 0 and to_hits > 0)
                    or (wds_src_hits > 0 and wds_dst_hits > 0)
                )

                # FILTRO LAN FISICO/DS:
                # Address3 in UNA SOLA direzione non prova un dispositivo Ethernet.
                # Può essere un client collegato a un altro BSSID/banda dello stesso
                # modem/router e bridgiato attraverso il Distribution System.
                #
                # Per mostrare il MAC nella tabella LAN richiediamo almeno una
                # evidenza indipendente:
                #   - presenza in ENTRAMBE le direzioni DS, oppure
                #   - ARP/Ethernet decodificabile, oppure
                #   - WDS sorgente+destinazione.
                # Questo elimina la massa di falsi LAN generata dai client Wi-Fi
                # presenti su altri BSSID del medesimo router.
                ds_lan_confirmed = bool(
                    bidirectional
                    or arp_hits > 0
                    or eth_hits > 0
                    or (wds_src_hits > 0 and wds_dst_hits > 0)
                )

                # Confidenza LAN/DS basata SOLO su evidenze del BSSID nel PCAP.
                # Address3 ripetuto è la prova principale; entrambe le direzioni,
                # ARP/Ethernet decodificabili, durata e volume aumentano la confidenza.
                duration=0.0
                if rec.get("first_ts") is not None and rec.get("last_ts") is not None:
                    duration=max(0.0,float(rec["last_ts"])-float(rec["first_ts"]))

                # ----------------------------------------------------------
                # LAN ALGORITHM V2
                # ----------------------------------------------------------
                # Lo score non somma più in modo cumulativo soglie dello stesso
                # tipo di evidenza: 50 frame Address3 non devono valere quanto
                # più fonti indipendenti (ARP/Ethernet/bidirezionalità/WDS).
                lan_score=0

                # 1) Evidenza DS primaria: progressiva ma NON cumulativa.
                if ds_hits >= 50:
                    ds_score = 45
                elif ds_hits >= 10:
                    ds_score = 35
                elif ds_hits >= 3:
                    ds_score = 22
                elif ds_hits >= 1:
                    ds_score = 12
                else:
                    ds_score = 0
                lan_score += ds_score

                # 2) Evidenze indipendenti e più forti.
                if bidirectional:
                    lan_score += 22
                if wds_src_hits and wds_dst_hits:
                    lan_score += 14
                elif wds_src_hits or wds_dst_hits:
                    lan_score += 7
                if arp_hits:
                    lan_score += 18
                if eth_hits:
                    lan_score += 12

                # Bonus sinergici: più fonti diverse valgono più della ripetizione
                # dello stesso pattern Address3.
                independent_sources = 0
                if bidirectional: independent_sources += 1
                if arp_hits: independent_sources += 1
                if eth_hits: independent_sources += 1
                if wds_src_hits or wds_dst_hits: independent_sources += 1
                if bcast_hits: independent_sources += 1

                if independent_sources >= 3:
                    lan_score += 10
                elif independent_sources >= 2:
                    lan_score += 6

                # 3) Broadcast: indizio debole, mai decisivo da solo.
                if bcast_hits >= 5:
                    lan_score += 5
                elif bcast_hits >= 1:
                    lan_score += 3

                # 4) Durata e volume: solo supporto, con soglie progressive.
                if duration >= 60:
                    lan_score += 8
                elif duration >= 30:
                    lan_score += 5
                elif duration >= 10:
                    lan_score += 2

                observed_bytes = int(rec.get("bytes",0))
                if observed_bytes >= 1_000_000:
                    lan_score += 8
                elif observed_bytes >= 100_000:
                    lan_score += 5
                elif observed_bytes >= 10_000:
                    lan_score += 2

                # 5) ALGORITMO LAN A BASSO TRAFFICO
                # ----------------------------------------------------------
                # Un dispositivo LAN quasi inattivo può generare pochissimi frame
                # (ARP, keepalive, DNS, beacon applicativi, polling sporadico).
                # Non aumentiamo semplicemente il peso di 1 singolo Address3:
                # cerchiamo invece coerenza temporale e/o più tipi di evidenza.
                low_traffic = (
                    ds_hits <= 8
                    and observed_bytes < 50_000
                )
                low_traffic_bonus = 0
                low_traffic_reasons = []

                if low_traffic:
                    # Due o più apparizioni distanziate nel tempo sono molto più
                    # informative di due frame consecutivi dello stesso burst.
                    if ds_hits >= 3 and duration >= 15:
                        low_traffic_bonus += 22
                        low_traffic_reasons.append("SPARSE-TEMPORAL")
                    elif ds_hits >= 2 and duration >= 8:
                        low_traffic_bonus += 16
                        low_traffic_reasons.append("SPARSE-TEMPORAL")

                    # ARP/Ethernet hanno un forte valore anche con pochi pacchetti.
                    if arp_hits and ds_hits <= 5:
                        low_traffic_bonus += 10
                        low_traffic_reasons.append("SPARSE-ARP")
                    if eth_hits and ds_hits <= 5:
                        low_traffic_bonus += 8
                        low_traffic_reasons.append("SPARSE-ETH")

                    # Broadcast proveniente dal lato DS è utile come supporto,
                    # ma non deve mai bastare da solo.
                    if bcast_hits and ds_hits >= 2:
                        low_traffic_bonus += 5
                        low_traffic_reasons.append("SPARSE-BCAST")

                    # Bonus limitato: evita che poco traffico diventi automaticamente
                    # "alta confidenza" senza prove indipendenti.
                    lan_score += min(28, low_traffic_bonus)

                # 6) Penalità per evidenza troppo debole/isolata.
                # Un singolo frame DS senza altre prove resta volutamente debole.
                if ds_hits == 1 and not bidirectional and not arp_hits and not eth_hits and not (wds_src_hits or wds_dst_hits):
                    lan_score = min(lan_score, 24)

                lan_score=min(100,max(0,lan_score))

                # FILTRO LAN PASSIVO STRICT / ALTA PRECISIONE
                # ----------------------------------------------------------
                # Obiettivo: minimizzare i falsi positivi.
                #
                # Regola fondamentale:
                # una comparsa monodirezionale in Address3 NON basta mai per
                # pubblicare un dispositivo come LAN, anche se ripetuta a lungo.
                # Un client Wi-Fi su un'altra radio/BSSID dello stesso bridge
                # può infatti apparire esattamente in quel modo.
                #
                # Un candidato viene pubblicato soltanto quando:
                #   1) non è mai stato visto direttamente come station radio;
                #   2) esiste evidenza DS in ENTRAMBE le direzioni;
                #   3) l'evidenza non è un singolo episodio ambiguo:
                #      almeno 4 hit DS totali, oppure almeno 2 hit distribuiti
                #      su >=5 secondi;
                #   4) ARP/Ethernet/broadcast/durata/volume possono aumentare
                #      lo score, ma NON possono sostituire la bidirezionalità.
                #
                # Questo è volutamente conservativo: può perdere un host LAN
                # completamente silenzioso o osservato in una sola direzione,
                # ma evita di trasformare client Wi-Fi bridgiati in falsi LAN.
                if mac in self.wifi_radio_macs_session:
                    # MODALITÀ DIAGNOSTICA "MOSTRA TUTTO":
                    # non nascondere il MAC se possiede evidenza DS; segnalarlo
                    # però con score basso perché esiste anche prova radio Wi-Fi.
                    if ds_hits > 0:
                        cls = "LAN CANDIDATO"
                        lan_score = min(max(lan_score, 5), 20)
                    else:
                        cls = "ALTRO/INCERTO"
                        lan_score = min(lan_score, 4)
                else:
                    classic_bidir = bool(from_hits > 0 and to_hits > 0)
                    wds_bidir = bool(wds_src_hits > 0 and wds_dst_hits > 0)
                    strict_bidir = bool(classic_bidir or wds_bidir)

                    repeated_bidir = bool(
                        strict_bidir
                        and (
                            ds_hits >= 4
                            or (ds_hits >= 2 and duration >= 5.0)
                        )
                    )

                    # RECUPERO PASSIVO MONODIREZIONALE AD ALTA PRECISIONE.
                    #
                    # Il PCAP reale può contenere host LAN molto silenziosi che
                    # trasmettono soltanto in una direzione durante il campione.
                    # Richiedere SEMPRE entrambe le direzioni li eliminava tutti.
                    #
                    # Accettiamo quindi anche un endpoint FromDS monodirezionale,
                    # ma SOLO se:
                    #   - non è mai comparso come station radio;
                    #   - ci sono almeno 4 osservazioni indipendenti;
                    #   - sono distribuite su almeno 20 secondi;
                    #   - non è un indirizzo multicast/broadcast;
                    #   - non stiamo osservando una topologia sibling-radio/mesh
                    #     che renderebbe Address3 ambiguo.
                    #
                    # FromDS è volutamente più affidabile di ToDS per questo
                    # recupero: Address3 rappresenta la sorgente lato DS che sta
                    # realmente inviando traffico verso una station Wi-Fi.
                    # Profilo PASSIVO ottimizzato per una finestra di ~2 minuti.
                    #
                    # Il PCAP reale mostra endpoint LAN embedded molto silenziosi:
                    # possono generare pochi broadcast/multicast FromDS, concentrati
                    # in due soli "episodi" separati di circa un minuto. Richiedere
                    # 3 bucket temporali eliminava quindi dispositivi LAN reali.
                    #
                    # Recupero conservativo:
                    #   - solo FromDS (MAC sorgente lato Distribution System);
                    #   - almeno 4 osservazioni;
                    #   - almeno 2 finestre temporali distinte da 20 s;
                    #   - almeno 45 s tra prima e ultima osservazione;
                    #   - nessuna prova che il MAC sia una station Wi-Fi;
                    #   - nessuna topologia sibling-radio/mesh ambigua.
                    #
                    # Il numero di frame NON basta da solo: la separazione temporale
                    # è ciò che impedisce a un singolo burst di diventare "LAN".
                    activity_bins20 = len(rec.get("_activity_bins20", set()) or set())
                    sparse_fromds_confirmed = bool(
                        not bridge_sibling_radios
                        and from_hits >= 4
                        and to_hits == 0
                        and wds_src_hits == 0
                        and wds_dst_hits == 0
                        and duration >= 45.0
                        and activity_bins20 >= 2
                        and mac not in self.wifi_radio_macs_session
                    )

                    # In presenza di radio sorelle/mesh alziamo ancora la soglia:
                    # la sola evidenza monodirezionale NON viene mai promossa.
                    if bridge_sibling_radios:
                        strict_confirmed = bool(
                            strict_bidir
                            and (
                                ds_hits >= 8
                                or (ds_hits >= 4 and duration >= 5.0)
                            )
                        )
                    else:
                        strict_confirmed = bool(repeated_bidir or sparse_fromds_confirmed)

                    if strict_confirmed:
                        cls = "LAN CANDIDATO"

                        if sparse_fromds_confirmed and not strict_bidir:
                            # Endpoint DS persistente ma visto in una sola direzione.
                            # Due episodi separati nel tempo sono una prova migliore
                            # di un burst, ma restiamo sotto una conferma bidirezionale.
                            lan_score = max(lan_score, 62)

                        # Una conferma bidirezionale reale parte da confidenza
                        # medio-alta; le evidenze indipendenti già calcolate sopra
                        # possono portarla più in alto.
                        if strict_bidir:
                            lan_score = max(lan_score, 68)

                        if ds_hits >= 10:
                            lan_score = max(lan_score, 76)
                        if duration >= 15.0 and ds_hits >= 4:
                            lan_score = max(lan_score, 80)
                        if (arp_hits or eth_hits) and ds_hits >= 4:
                            lan_score = max(lan_score, 84)
                    else:
                        # WIFI_425 - filtro anti-falso-LAN:
                        # un endpoint visto soltanto in Address3/Address4 lato DS NON
                        # viene piu' promosso a LAN solo per scopi diagnostici.
                        # Su router dual-band/mesh questo pattern puo' appartenere a
                        # un client Wi-Fi collegato alla radio sorella.
                        cls = "ALTRO/INCERTO"
                        lan_score = min(lan_score, 14)

                # Invariante finale: una station osservata direttamente via radio
                # in qualunque momento della sessione non puo' essere un dispositivo
                # della tabella LAN. Questo blocca anche eventuali ripromozioni da
                # euristiche successive o da risultati cumulativi.
                if cls == "LAN CANDIDATO" and mac in set(getattr(self, "wifi_radio_macs_session", set()) or set()):
                    cls = "ALTRO/INCERTO"
                    lan_score = min(lan_score, 14)

                # WIFI_438 - FIX LAN DUAL-BAND / ROUTER IN CASCATA
                # ----------------------------------------------------------
                # Una radio sorella 2.4/5 GHz e' un fattore di AMBIGUITA', non un
                # veto assoluto dopo che il candidato ha gia' superato il filtro
                # LAN strict. Il vecchio blocco retrocedeva TUTTI i MAC DS a
                # ALTRO/INCERTO quando esisteva un BSSID sibling, annullando la
                # prova bidirezionale appena calcolata. Su AP/router dual-band
                # questo faceva sparire host LAN reali dietro il bridge/router.
                #
                # Manteniamo quindi la classificazione LAN se esiste una prova
                # indipendente e forte lato DS (bidirezionale, WDS bidirezionale,
                # ARP o Ethernet). Applichiamo solo una piccola penalita' allo
                # score per rappresentare l'ambiguita' residua. I MAC osservati
                # direttamente come station Wi-Fi restano comunque esclusi dal
                # blocco invariante immediatamente precedente.
                if (
                    cls == "LAN CANDIDATO"
                    and mac in set(getattr(self, "_lan_sibling_radio_ambiguous_macs", set()) or set())
                ):
                    sibling_ds_disambiguated = bool(
                        (from_hits > 0 and to_hits > 0 and (ds_hits >= 4 or duration >= 5.0))
                        or (wds_src_hits > 0 and wds_dst_hits > 0)
                        or arp_hits > 0
                        or eth_hits > 0
                    )
                    if sibling_ds_disambiguated:
                        # Ambiguita' dual-band: riduzione di confidenza, NON veto.
                        lan_score = max(0, int(lan_score) - 6)
                        rec["_dual_band_ds_disambiguated"] = True
                    else:
                        cls = "ALTRO/INCERTO"
                        lan_score = min(lan_score, 14)

                if lan_score >= 75:
                    confidence="HIGH" if is_en else "ALTA"
                elif lan_score >= 45:
                    confidence="MODERATE" if is_en else "MEDIA"
                else:
                    confidence="LOW" if is_en else "BASSA"

                # Sottotipo più informativo, con categoria specifica per host
                # LAN quasi inattivi ma coerenti nel tempo.
                low_traffic_confirmed = bool(
                    cls == "LAN CANDIDATO"
                    and low_traffic
                    and low_traffic_bonus >= 16
                    and ds_hits >= 2
                    and bidirectional
                )

                if low_traffic_confirmed:
                    lan_kind = (
                        "LOW-TRAFFIC LAN PROBABLE"
                        if is_en else
                        "LAN BASSO TRAFFICO PROBABILE"
                    )
                elif (arp_hits or eth_hits) and lan_score >= 60:
                    lan_kind = "LAN/ETHERNET PROBABLE" if is_en else "LAN/ETHERNET PROBABILE"
                elif lan_score >= 45:
                    lan_kind = "DS PROBABLE" if is_en else "DS PROBABILE"
                else:
                    lan_kind = "DS POSSIBLE" if is_en else "DS POSSIBILE"

                parts=[]
                if mac in set(getattr(self, "_lan_sibling_radio_ambiguous_macs", set()) or set()):
                    parts.append(
                        "SIBLING-RADIO AMBIGUOUS"
                        if is_en else
                        "RADIO-SORELLA AMBIGUA"
                    )
                if from_hits: parts.append(f"FromDS-Addr3-SRC {from_hits}")
                if to_hits: parts.append(f"ToDS-Addr3-DST {to_hits}")
                if wds_src_hits: parts.append(f"WDS-Addr4-SRC {wds_src_hits}")
                if wds_dst_hits: parts.append(f"WDS-Addr3-DST {wds_dst_hits}")
                if bcast_hits: parts.append(f"BROADCAST-SRC {bcast_hits}")
                if eth_hits: parts.append(f"Ethernet {eth_hits}")
                if arp_hits: parts.append(f"ARP {arp_hits}")
                if low_traffic_reasons:
                    parts.append(
                        ("LOW-TRAFFIC " if is_en else "BASSO-TRAFFICO ")
                        + "+".join(low_traffic_reasons)
                    )
                if ds_hits == 1 and not bidirectional and not eth_hits and not arp_hits and not (wds_src_hits or wds_dst_hits):
                    parts.append("SINGLE INDICATOR" if is_en else "EVIDENZA SINGOLA")
                if cls != "LAN CANDIDATO":
                    evidence = (
                        f"DS-ENDPOINT {lan_score}/100 | "
                        + (", ".join(parts) or "DS")
                    )
                    notes = (
                        "DS endpoint not yet strong enough for the LAN table, or directly observed as a Wi-Fi radio station."
                        if is_en else
                        "Endpoint DS non ancora abbastanza forte per la tabella LAN, oppure osservato direttamente come station Wi-Fi."
                    )
                else:
                    evidence=f"{confidence} {lan_score}/100 | {lan_kind} | " + (", ".join(parts) or "DS")
                if cls == "LAN CANDIDATO" and is_en:
                    notes=(
                        "MAC address observed as a Distribution System (DS)-side endpoint; "
                        f"classification={lan_kind}, DS indicators={ds_hits}, observed duration={duration:.1f}s, observed bytes={int(rec.get('bytes',0))}. "
                        "Automatically excluded if it also appears as a Wi-Fi station. "
                        "Classification is based on IEEE 802.11 header fields for the selected BSSID, "
                        "which remain observable without the WPA/WPA2 passphrase. It indicates a DS-side "
                        "endpoint, but does not by itself prove a physical Ethernet connection."
                    )
                elif cls == "LAN CANDIDATO":
                    notes=(
                        "MAC osservato come endpoint del Distribution System; "
                        f"classificazione={lan_kind}, evidenze={ds_hits}, durata={duration:.1f}s, byte osservati={int(rec.get('bytes',0))}. "
                        "Escluso automaticamente se compare anche come station Wi-Fi. "
                        "Classificazione basata sugli header 802.11 del BSSID nel PCAP, "
                        "leggibili anche senza password WPA/WPA2. Indica un endpoint lato "
                        "Distribution System, ma non può dimostrare da sola il collegamento fisico Ethernet."
                    )

            else:
                cls="ALTRO/INCERTO"
                evidence=("present in the PCAP without an unambiguous role" if is_en else "presenza nel PCAP senza ruolo univoco")
                notes=("Role cannot be determined with confidence" if is_en else "Ruolo non determinabile con sicurezza")

            if client and mac == client:
                notes += ("; selected client" if is_en else "; client selezionato")

            if cls == "MULTICAST/BROADCAST":
                vendor=("Service" if is_en else "Servizio")
            else:
                # Nessuna chiamata Internet durante la cattura/analisi:
                # evita blocchi di diversi secondi per ogni MAC sconosciuto.
                vendor=cache.get(mac.lower(), "Unknown" if is_en else "Sconosciuto")
                if vendor in ("Sconosciuto","Unknown",""):
                    # Fallback locale Wireshark/OUI: nessuna richiesta Internet.
                    try:
                        oui_cache=self._load_tshark_manuf_cache()
                        oui=":".join(mac.upper().split(":")[:3])
                        rec_vendor=oui_cache.get(oui)
                        if rec_vendor:
                            short_name,long_name=rec_vendor
                            vendor=(long_name or short_name or ("Unknown" if is_en else "Sconosciuto")).strip()
                    except Exception:
                        pass
            out.append((mac,vendor,cls,evidence,notes))

        if lan_candidates:
            self.logmsg(
                ("LAN-side candidates from ToDS/FromDS/WDS mapping (Address 3/Address 4): " if is_en
                 else "LAN candidati da mapping ToDS/FromDS/WDS (Address3/Address4): ")
                + ", ".join(sorted(lan_candidates))
            )
        else:
            self.logmsg(
                f"No LAN/DS endpoint was observed. LAN visibility: {getattr(self,'lan_observability',{}).get('level','N/A')}. "                 "No candidates does not rule out devices connected to the router's wired LAN ports."
                if is_en else
                f"Nessun endpoint LAN/DS osservato. Visibilita' LAN: {getattr(self,'lan_observability',{}).get('level','N/D')}. "                 "L'assenza di candidati non esclude dispositivi collegati alle porte LAN del router."
            )

        return out

    def _lan_score_from_evidence(self, evidence):
        try:
            m=re.search(r"(\d{1,3})/100", str(evidence))
            return max(0,min(100,int(m.group(1)))) if m else 0
        except Exception:
            return 0

    def _lan_level_from_score(self, score):
        try:
            score=int(score)
        except Exception:
            score=0
        is_en=getattr(self,"language","it") == "en"
        if score >= 75:
            return "HIGH" if is_en else "ALTA"
        if score >= 45:
            return "MODERATE" if is_en else "MEDIA"
        return "LOW" if is_en else "BASSA"


    def _lan_text_for_language(self, value):
        """Translate LAN evidence generated internally into technical English when GUI is EN."""
        s=str(value or "")
        if getattr(self,"language","it") != "en":
            return s

        replacements=[
            ("MOLTO PROBABILE", "HIGHLY LIKELY"),
            ("PROBABILE", "LIKELY"),
            ("POSSIBILE", "POSSIBLE"),
            ("DA OSSERVARE", "LOW CONFIDENCE"),
            ("ALTA", "HIGH"),
            ("MEDIA", "MODERATE"),
            ("BASSA", "LOW"),
            ("EVIDENZA SINGOLA", "SINGLE INDICATOR"),
            ("MAC osservato come endpoint lato Distribution System",
             "MAC address observed as a Distribution System (DS)-side endpoint"),
            ("Router/access point oggetto della cattura",
             "Router/access point being captured"),
            ("Indirizzo gruppo/servizio",
             "Group/service address"),
            ("Non contato come dispositivo",
             "Not counted as a device"),
            ("Unknown", "Unknown"),
            ("durata=", "observed duration="),
            ("byte osservati=", "observed bytes="),
        ]
        for a,b in replacements:
            s=s.replace(a,b)
        return s

    def _lan_reasons_from_evidence(self, evidence, notes=""):
        """Traduce le evidenze tecniche LAN in motivazioni leggibili."""
        ev=str(evidence or "")
        is_en=getattr(self,"language","it") == "en"
        reasons=[]

        def add(it,en):
            reasons.append(en if is_en else it)

        m=re.search(r"FromDS-Addr3-SRC\s+(\d+)",ev)
        if m:
            add(
                f"MAC osservato {m.group(1)} volte come sorgente Address3 in frame FromDS",
                f"MAC address observed {m.group(1)} times as the Address 3 source in From-DS frames"
            )
        m=re.search(r"ToDS-Addr3-DST\s+(\d+)",ev)
        if m:
            add(
                f"MAC osservato {m.group(1)} volte come destinazione Address3 in frame ToDS",
                f"MAC address observed {m.group(1)} times as the Address 3 destination in To-DS frames"
            )
        m=re.search(r"WDS-Addr4-SRC\s+(\d+)",ev)
        if m:
            add(
                f"Presenza WDS Address4 come sorgente: {m.group(1)} osservazioni",
                f"WDS Address 4 source observations: {m.group(1)} observations"
            )
        m=re.search(r"WDS-Addr3-DST\s+(\d+)",ev)
        if m:
            add(
                f"Presenza WDS Address3 come destinazione: {m.group(1)} osservazioni",
                f"WDS Address 3 destination observations: {m.group(1)} observations"
            )
        m=re.search(r"BROADCAST-SRC\s+(\d+)",ev)
        if m:
            add(
                f"Traffico broadcast riconducibile al MAC: {m.group(1)} osservazioni",
                f"Broadcast-source observations attributed to this MAC address: {m.group(1)}"
            )
        m=re.search(r"Ethernet\s+(\d+)",ev)
        if m:
            add(
                f"Indizi Ethernet decodificabili: {m.group(1)}",
                f"Decodable Ethernet-layer indicators: {m.group(1)}"
            )
        m=re.search(r"ARP\s+(\d+)",ev)
        if m:
            add(
                f"Indizi ARP osservati: {m.group(1)}",
                f"ARP-related indicators observed: {m.group(1)}"
            )
        if "EVIDENZA SINGOLA" in ev or "SINGLE INDICATOR" in ev:
            add(
                "È presente una sola evidenza DS: classificazione da considerare debole",
                "Only one DS-side indicator is present; confidence in this classification is low"
            )

        if "LAN/ETHERNET PROBABILE" in ev or "LAN/ETHERNET PROBABLE" in ev:
            add(
                "Più evidenze indipendenti sono compatibili con un endpoint LAN/Ethernet dietro l'AP",
                "Multiple independent indicators are compatible with a LAN/Ethernet endpoint behind the AP"
            )
        elif "DS PROBABILE" in ev or "DS PROBABLE" in ev:
            add(
                "Il MAC è probabilmente un endpoint lato Distribution System",
                "The MAC address is probably a Distribution System-side endpoint"
            )
        elif "DS POSSIBILE" in ev or "DS POSSIBLE" in ev:
            add(
                "Il MAC è un possibile endpoint lato Distribution System, ma le evidenze sono ancora limitate",
                "The MAC address is a possible Distribution System-side endpoint, but evidence is still limited"
            )

        n=str(notes or "")
        md=(re.search(r"durata=([0-9.]+)s",n)
            or re.search(r"observed duration=([0-9.]+)s",n))
        mb=(re.search(r"byte osservati=(\d+)",n)
            or re.search(r"observed bytes=(\d+)",n))
        if md:
            add(
                f"Presenza osservata per circa {md.group(1)} secondi",
                f"Observed duration: approximately {md.group(1)} seconds"
            )
        if mb:
            add(
                f"Volume osservato: {int(mb.group(1)):,} byte".replace(",","."),
                f"Observed traffic volume: {int(mb.group(1)):,} bytes"
            )

        if not reasons:
            add(
                "Il MAC è stato osservato lato Distribution System negli header 802.11",
                "The MAC address was observed on the Distribution System (DS) side in IEEE 802.11 header fields"
            )
        return reasons

    def update_probable_lan_vendors(self, observed_rows):
        """
        Modalità LAN BILANCIATA.
        Mostra endpoint DS coerenti che NON risultano direttamente come station
        Wi-Fi su nessun BSSID osservato nel PCAP.
        """
        if not hasattr(self, "lan_vendor_tree"):
            return

        wifi_scanner_macs=set()
        try:
            for item in self.client_tree.get_children():
                vals=self.client_tree.item(item,"values")
                if not vals:
                    continue
                mac=str(vals[0]).strip().lower()
                if MAC_FULL.match(mac):
                    wifi_scanner_macs.add(mac)
        except Exception:
            pass

        # Prova radio ricavata direttamente dal PCAP. Ha precedenza assoluta
        # rispetto alla scansione IP locale e resta valida per tutta la sessione.
        radio_session = set(getattr(self, "wifi_radio_macs_session", set()) or set())

        # FILTRO ANTI-FALSI-POSITIVI WIFI -> LAN.
        #
        # Un MAC visto direttamente come station 802.11 NON può restare nella
        # tabella "POSSIBILI DISPOSITIVI LAN", anche se compare anche come
        # Address3/Address4 lato Distribution System. Questo caso è normale con
        # modem dual-band/mesh/bridge: un client Wi-Fi di un'altra radio può
        # transitare nel DS e sembrare, erroneamente, un host Ethernet.
        #
        # Le fonti hanno questa priorità:
        #   1) prova radio diretta conservata per tutta la cattura;
        #   2) tabella CLIENT dello scanner;
        #   3) righe correnti già classificate Wi-Fi ASSOCIATO.
        wifi_rows_now=set()
        try:
            for _row in observed_rows or []:
                if len(_row) >= 3 and str(_row[2]) == "Wi-Fi ASSOCIATO":
                    _m=str(_row[0]).strip().lower()
                    if MAC_FULL.match(_m):
                        wifi_rows_now.add(_m)
        except Exception:
            pass

        wifi_global=set(getattr(self,"wifi_radio_macs_global",set()) or set())
        try:
            wifi_global.update(radio_session)
            wifi_global.update(wifi_scanner_macs)
            wifi_global.update(wifi_rows_now)
            self.wifi_radio_macs_global=wifi_global
        except Exception:
            pass

        try:
            _current_bssid=self._dual_band_value(getattr(self,"bssid",""))
        except Exception:
            _current_bssid=""
        related_radio_bssids=self._related_radio_bssids(_current_bssid)
        infrastructure_bssids=set(self._known_ap_bssids())
        if MAC_FULL.match(_current_bssid):
            infrastructure_bssids.add(_current_bssid)

        wifi_station_macs = (
            set(radio_session) | set(wifi_scanner_macs) | wifi_rows_now | set(wifi_global)
        )
        # Solo AP/BSSID/radio-infrastruttura vengono esclusi in modo assoluto.
        # Una station Wi-Fi che compare ANCHE come endpoint DS resta visibile come
        # candidato LAN/bridge a bassa confidenza, secondo la politica di sensibilita'.
        hard_excluded_macs = set(related_radio_bssids) | set(infrastructure_bssids)
        wifi_excluded_macs = set(wifi_station_macs) | set(hard_excluded_macs)

        # Pulizia mirata: se un MAC era stato mostrato come LAN nei primi secondi
        # della cattura e successivamente viene provato come station Wi-Fi, viene
        # eliminato SUBITO da tutte le cache LAN sticky.
        if not isinstance(getattr(self, "lan_persistent_rows", None), dict):
            self.lan_persistent_rows = {}
        if not isinstance(getattr(self, "lan_persistent_details", None), dict):
            self.lan_persistent_details = {}

        # Pulizia solo dell'infrastruttura radio. Le station con doppia evidenza
        # Wi-Fi+DS restano visibili, ma con score basso e nota di ambiguita'.
        _radio_now = set(hard_excluded_macs)
        for _mac in list(self.lan_persistent_rows):
            _det = self.lan_persistent_details.get(_mac, {}) or {}
            _src = str(_det.get("source", "")).upper()
            _is_gw = bool(_det.get("is_gateway")) or _src == "DEFAULT-GATEWAY"
            if _mac in _radio_now and not _is_gw:
                self.lan_persistent_rows.pop(_mac, None)
                self.lan_persistent_details.pop(_mac, None)
                try:
                    self.lan_seen_rows.pop(_mac, None)
                except Exception:
                    pass
                try:
                    self.lan_candidate_details.pop(_mac, None)
                except Exception:
                    pass

        try:
            _removed_wifi_lan = sorted(
                _m for _m in wifi_excluded_macs
                if _m in (set(getattr(self, "live_mac_rows", {}) or {}) | set(wifi_scanner_macs) | set(radio_session))
            )
            if _removed_wifi_lan:
                self.logmsg(
                    ("LAN filter: Wi-Fi stations excluded from LAN candidates: "
                     if getattr(self,"language","it")=="en" else
                     "Filtro LAN: station Wi-Fi escluse dai candidati LAN: ")
                    + ", ".join(_removed_wifi_lan)
                )
        except Exception:
            pass

        current={}
        details={}
        for row in observed_rows or []:
            if len(row) < 5:
                continue
            mac,vendor,cls,evidence,notes=row[:5]
            if str(cls) != "LAN CANDIDATO":
                continue

            mac=str(mac).lower()
            if not MAC_FULL.match(mac) or self.is_multicast_or_broadcast(mac):
                continue
            if mac in hard_excluded_macs:
                # Un BSSID/AP/radio nota e' infrastruttura, non un host LAN.
                continue

            score=self._lan_score_from_evidence(evidence)
            if mac in wifi_station_macs:
                # Doppia evidenza: non nascondere il MAC. Possibile bridge/mesh o
                # classificazione ambigua; resta nella fascia bassa.
                score = min(max(score, 5), 20)
                evidence = str(evidence) + (" | WIFI/DS AMBIGUOUS" if getattr(self,"language","it")=="en" else " | WIFI/DS AMBIGUO")
                notes = str(notes) + (
                    " Also observed as a Wi-Fi station; kept as a low-confidence LAN/bridge candidate."
                    if getattr(self,"language","it")=="en" else
                    " Osservato anche come station Wi-Fi; mantenuto come possibile LAN/bridge a bassa confidenza."
                )

            # Conferma dinamica LOW-TRAFFIC:
            # il candidato guadagna fiducia solo se, tra aggiornamenti successivi,
            # compaiono NUOVE evidenze DS nel file di cattura. Un refresh identico
            # non incrementa nulla.
            if not isinstance(getattr(self, "lan_low_traffic_history", None), dict):
                self.lan_low_traffic_history = {}

            _m_ds = re.search(r"(?:DS indicators=|evidenze=)(\d+)", str(notes), re.I)
            _m_bytes = re.search(r"(?:observed bytes=|byte osservati=)(\d+)", str(notes), re.I)
            _ds_now = int(_m_ds.group(1)) if _m_ds else 0
            _bytes_now = int(_m_bytes.group(1)) if _m_bytes else 0

            _hist = self.lan_low_traffic_history.get(mac, {
                "ds": _ds_now,
                "bytes": _bytes_now,
                "growth": 0
            })
            if _ds_now > int(_hist.get("ds", 0)) or _bytes_now > int(_hist.get("bytes", 0)):
                _hist["growth"] = int(_hist.get("growth", 0)) + 1
            _hist["ds"] = max(_ds_now, int(_hist.get("ds", 0)))
            _hist["bytes"] = max(_bytes_now, int(_hist.get("bytes", 0)))
            self.lan_low_traffic_history[mac] = _hist

            _is_sparse = _ds_now > 0 and _ds_now <= 8 and _bytes_now < 50000
            if _is_sparse and int(_hist.get("growth", 0)) >= 2 and score < 70:
                # Crescita lenta ma reale osservata in più momenti della cattura.
                score = min(70, score + 12)
                if getattr(self,"language","it")=="en":
                    evidence = str(evidence) + " | SLOW-GROWTH CONFIRMED"
                    notes = str(notes) + " Repeated sparse DS activity increased over time."
                else:
                    evidence = str(evidence) + " | CRESCITA-LENTA CONFERMATA"
                    notes = str(notes) + " Attività DS sporadica ma realmente aumentata nel tempo."

            level=self._lan_level_from_score(score)
            gateway_info = getattr(self, "lan_gateway_info", {}) or {}
            gw_ip = str(gateway_info.get("ip","")).strip()
            gw_mac = str(gateway_info.get("mac","")).strip().lower()
            is_gateway = bool(gw_mac and mac == gw_mac)
            role = (
                "ROUTER"
                if is_gateway else
                "LAN"
            )
            if is_gateway:
                score = 100
                level = "PRIMARY GATEWAY" if getattr(self,"language","it")=="en" else "GATEWAY PRINCIPALE"
            display=(str(vendor),mac,f"{score}/100",level,role)
            current[mac]=display
            details[mac]={
                "mac":mac,
                "vendor":str(vendor),
                "score":score,
                "level":level,
                "evidence":str(evidence),
                "notes":str(notes),
                "role":role,
                "is_gateway":is_gateway,
                "gateway_ip":gw_ip,
                "gateway_mac":gw_mac,
                "reasons":self._lan_reasons_from_evidence(evidence,notes),
            }

        if not isinstance(getattr(self,"lan_seen_rows",None),dict):
            self.lan_seen_rows={}
        if not isinstance(getattr(self,"lan_candidate_details",None),dict):
            self.lan_candidate_details={}

        for mac in list(self.lan_seen_rows):
            if mac in hard_excluded_macs:
                self.lan_seen_rows.pop(mac,None)
                self.lan_candidate_details.pop(mac,None)

        for mac,row in current.items():
            old=self.lan_seen_rows.get(mac)
            old_score=self._lan_score_from_evidence(old[2] if old and len(old)>2 else "")
            new_score=self._lan_score_from_evidence(row[2])
            if old is None or new_score >= old_score:
                self.lan_seen_rows[mac]=row
                self.lan_candidate_details[mac]=details[mac]

        # Memoria persistente della sessione:
        # una volta che un dispositivo è stato mostrato come LAN, NON viene più
        # rimosso durante gli aggiornamenti live. Sparirà solo all'avvio di una
        # nuova cattura, quando _clear_capture_results_on_start() azzera la cache.
        if not isinstance(getattr(self,"lan_persistent_rows",None),dict):
            self.lan_persistent_rows={}
        if not isinstance(getattr(self,"lan_persistent_details",None),dict):
            self.lan_persistent_details={}

        # Integrazione della seconda scansione: conserva anche i LAN della prima.
        try:
            for _m,_r in (getattr(self, "_cascade_first_lan_rows", {}) or {}).items():
                self.lan_persistent_rows.setdefault(_m, _r)
            for _m,_d in (getattr(self, "_cascade_first_lan_details", {}) or {}).items():
                self.lan_persistent_details.setdefault(_m, _d)
                self.lan_candidate_details.setdefault(_m, _d)
        except Exception:
            pass

        # Solo l'infrastruttura radio nota viene eliminata in modo assoluto.
        # Le station Wi-Fi con contemporanea evidenza DS restano come candidati
        # ambigui a bassa probabilita'.
        for mac in hard_excluded_macs:
            self.lan_seen_rows.pop(mac, None)
            self.lan_candidate_details.pop(mac, None)
            self.lan_persistent_rows.pop(mac, None)
            self.lan_persistent_details.pop(mac, None)
            try:
                self.active_lan_results.pop(mac, None)
            except Exception:
                pass
            self.lan_candidate_confirmations.pop(mac, None)
            self.lan_confirmed_visible.discard(mac)
            try:
                self.lan_low_traffic_history.pop(mac, None)
            except Exception:
                pass

        # Evidenza passiva DS già consolidata.
        for mac,row in self.lan_seen_rows.items():
            old = self.lan_persistent_rows.get(mac)
            old_score = self._lan_score_from_evidence(old[2] if old and len(old)>2 else "")
            new_score = self._lan_score_from_evidence(row[2] if len(row)>2 else "")
            # Come nelle versioni LAN precedenti: se il MAC è stato realmente
            # osservato lato DS nel PCAP, viene conservato; lo SCORE esprime poi
            # la forza dell'evidenza senza far sparire il MAC.
            if old is None or new_score >= old_score:
                self.lan_persistent_rows[mac] = row
                det = self.lan_candidate_details.get(mac)
                if det:
                    self.lan_persistent_details[mac] = det

        # MODALITA' SENSIBILITA': i candidati provenienti dalla discovery attiva
        # non vengono eliminati a priori; restano a score basso e con fonte esplicita.

        # LAN IBRIDA IN MODALITA' STRICT:
        # la discovery attiva serve a risolvere vendor/IP di candidati già provati
        # dal PCAP. Non viene più usata come prova autonoma di Ethernet/LAN,
        # perché ARP/ping non distinguono client Wi-Fi da host cablati.
        #
        # IMPORTANTE: "presente nella LAN IP locale" non significa prova fisica
        # assoluta del cavo Ethernet. La colonna RUOLO distingue infatti:
        # - GATEWAY PRINCIPALE
        # - LAN CONFERMATA DS (evidenza 802.11/DS)
        # - LAN ATTIVA BASSO TRAFFICO (presenza IP/ARP/neighbour)
        active_rows = getattr(self, "active_lan_results", {}) or {}

        for mac, rec_active in active_rows.items():
            mac = str(mac).lower()
            if not MAC_FULL.match(mac) or self.is_multicast_or_broadcast(mac):
                continue

            det = dict(rec_active.get("details") or {})
            row = rec_active.get("display")
            if not row:
                continue

            is_gateway_active = (
                bool(det.get("is_gateway"))
                or str(det.get("source","")).upper() == "DEFAULT-GATEWAY"
            )

            # Prova del ruolo Wi-Fi:
            # se il MAC è stato osservato direttamente come station radio del BSSID
            # oppure compare nella tabella CLIENT, NON deve essere importato come LAN.
            #
            # La discovery ARP/IP non distingue Ethernet da Wi-Fi. Un client Wi-Fi
            # risponde comunque ad ARP/ping e quindi apparirebbe falsamente "LAN"
            # se dessimo priorità alla sola discovery attiva.
            if not is_gateway_active and mac in hard_excluded_macs:
                continue

            vendor = str(
                det.get("vendor")
                or (row[0] if len(row) > 0 else "")
                or ""
            ).strip()
            if not vendor:
                vendor = "Unknown" if getattr(self,"language","it")=="en" else "Sconosciuto"

            if is_gateway_active:
                # Il gateway mantiene score/ruolo massimo.
                self.lan_persistent_rows[mac] = row
                self.lan_persistent_details[mac] = det
                continue

            # Host generico visto solo via discovery attiva: non e' prova fisica
            # di Ethernet, ma nella modalita' sensibilita' viene mostrato come
            # candidato LAN/IP a bassa confidenza invece di essere eliminato.
            active_score = 12 if mac in wifi_station_macs else 25
            active_level = self._lan_level_from_score(active_score)
            active_role = (
                "LAN/IP TO WATCH" if getattr(self,"language","it")=="en" else
                "LAN/IP DA OSSERVARE"
            )
            active_row = (vendor, mac, f"{active_score}/100", active_level, active_role)
            active_det = dict(det)
            active_det.update({
                "score": active_score,
                "level": active_level,
                "role": active_role,
                "source": "ACTIVE-LAN-LOW-TRAFFIC",
            })
            active_det["notes"] = str(active_det.get("notes", "")) + (
                " Active discovery alone cannot distinguish Ethernet from Wi-Fi; retained only as a low-confidence candidate."
                if getattr(self,"language","it")=="en" else
                " La sola discovery attiva non distingue Ethernet da Wi-Fi; mantenuto solo come candidato a bassa confidenza."
            )
            self.lan_persistent_rows[mac] = active_row
            self.lan_persistent_details[mac] = active_det
            self.lan_candidate_details[mac] = active_det

        # Mantiene disponibili anche i dettagli dei dispositivi già memorizzati.
        for mac,det in self.lan_persistent_details.items():
            self.lan_candidate_details[mac] = det

        # Il gateway resta protetto; gli host ACTIVE-LAN-LOW-TRAFFIC possono
        # rimanere visibili a bassa confidenza, salvo che siano infrastruttura AP.
        _lan_protected_active = set()
        for _mac, _det in self.lan_persistent_details.items():
            _src = str((_det or {}).get("source", "")).upper()
            if _src == "DEFAULT-GATEWAY":
                _lan_protected_active.add(_mac)

        merged = {
            mac: row for mac, row in self.lan_persistent_rows.items()
            if mac not in hard_excluded_macs or mac in _lan_protected_active
        }

        # Visualizzazione sensibile: conserva anche i candidati DS/Wi-Fi ambigui
        # e quelli della discovery attiva, con score/probabilita' ridotti.
        merged = {
            mac: row for mac, row in merged.items()
            if mac not in hard_excluded_macs or mac in _lan_protected_active
        }

        current_source = str(
            getattr(self, "_passive_current_source_label", "") or ""
        ).strip()

        if not isinstance(getattr(self, "_lan_display_sources", None), dict):
            self._lan_display_sources = {}

        # MAC realmente osservati nel segmento corrente.
        _lan_seen_now = set(current.keys())

        # Se la discovery attiva appartiene a una delle radio del livello
        # corrente, può aggiungere la stessa provenienza senza creare duplicati.
        try:
            _ainfo = getattr(self, "active_lan_scan_info", {}) or {}
            _atarget = str(
                _ainfo.get("target_bssid") or _ainfo.get("connected_bssid") or ""
            ).strip().lower()
            _stage_now = set(
                getattr(self, "_passive_router_stage_bssids", set()) or set()
            )
            if (
                not _atarget
                or _atarget == str(getattr(self, "_passive_current_source_bssid", "") or "").lower()
                or _atarget in _stage_now
            ):
                _lan_seen_now.update(
                    str(_m).lower()
                    for _m in (getattr(self, "active_lan_results", {}) or {})
                    if MAC_FULL.match(str(_m).lower())
                )
        except Exception:
            pass

        visible={}
        duplicate_items=[]
        for item in self.lan_vendor_tree.get_children():
            vals=tuple(self.lan_vendor_tree.item(item,"values") or ())
            if len(vals) < 5:
                continue
            mac0=str(vals[4]).lower()
            if mac0 in visible:
                # Ripulisce eventuali duplicati lasciati da versioni precedenti.
                duplicate_items.append(item)
            else:
                visible[mac0]=item
                old_src=str(vals[5] if len(vals)>5 else "").strip()
                if old_src:
                    self._lan_display_sources.setdefault(mac0, set()).update(
                        _s.strip() for _s in old_src.split(" ; ") if _s.strip()
                    )

        for _item in duplicate_items:
            try:
                self.lan_vendor_tree.delete(_item)
            except Exception:
                pass

        for mac,row in merged.items():
            _role = str(row[4] or "")
            try:
                _linked_parent = str(getattr(self, "_router_cam_link_parent_mac", "") or "").lower()
                _linked_bssid = str(getattr(self, "_router_cam_link_parent_bssid", "") or "").lower()
                _second_cams = getattr(self, "_cascade_second_scan_cameras", {}) or {}
                _is_linked_parent = (
                    str(mac).lower() in {_linked_parent, _linked_bssid}
                    or any(
                        str((_i or {}).get("parent_mac","")).lower() == str(mac).lower()
                        or str((_i or {}).get("parent_bssid","")).lower() == str(mac).lower()
                        for _i in _second_cams.values()
                    )
                )
                if _is_linked_parent and "(*)" not in _role:
                    _role = (_role + " (*)").strip()
            except Exception:
                pass
            if mac in _lan_seen_now and current_source:
                self._lan_display_sources.setdefault(mac, set()).add(current_source)

            _sources = sorted(
                self._lan_display_sources.get(mac, set()) or set()
            )
            _source_text = " ; ".join(_sources)

            display_row=(row[0],_role,row[3],row[2],row[1],_source_text)
            item=visible.get(mac)
            if item:
                if tuple(self.lan_vendor_tree.item(item,"values")[:6]) != tuple(display_row):
                    self.lan_vendor_tree.item(item,values=display_row)
            else:
                iid="lan_"+mac
                try:
                    self.lan_vendor_tree.insert("","end",iid=iid,values=display_row)
                except Exception:
                    self.lan_vendor_tree.insert("","end",values=display_row)
                visible[mac]=iid

        # Ordine: score più alto in cima.
        ordered=[]
        for item in self.lan_vendor_tree.get_children():
            vals=self.lan_vendor_tree.item(item,"values")
            score=self._lan_score_from_evidence(vals[3] if len(vals)>3 else "")
            mac=str(vals[4]) if len(vals)>4 else ""
            ordered.append((item,score,mac))
        for pos,(item,_score,_mac) in enumerate(sorted(ordered,key=lambda x:(-x[1],x[2]))):
            try:
                self.lan_vendor_tree.move(item,"",pos)
            except Exception:
                pass

        # Ridisegna il font compatto sotto SC e PROVENIENZA.
        try:
            self._refresh_lan_score_font_overlay()
        except Exception:
            pass

        label="Number" if getattr(self,"language","it")=="en" else "Numero"

        # Non lasciare il riquadro LAN apparentemente "vuoto senza motivo".
        # Se il PCAP non contiene frame DATA/DS, nessun algoritmo passivo può
        # ricavare gli host cablati dietro l'AP: ACK/beacon/probe non espongono
        # Address3/Address4 utili per gli endpoint del Distribution System.
        # Mostriamo quindi esplicitamente il grado di osservabilità invece di
        # far sembrare che "0" significhi "nessun dispositivo LAN esistente".
        _obs = getattr(self, "lan_observability", {}) or {}
        try:
            _ds_frames = int(_obs.get("ds_frames", 0) or 0)
            _endpoint_hits = int(_obs.get("endpoint_hits", 0) or 0)
        except Exception:
            _ds_frames = 0
            _endpoint_hits = 0
        _vis = str(_obs.get("level", "") or "").strip()

        if not merged and _ds_frames == 0:
            try:
                self.command_debug_write(
                    "[LAN] PCAP WITHOUT DATA/DS: wired cascade cannot be inferred from "
                    "the passive capture alone; ACTIVE-LAN/session CLIENT evidence is required."
                )
            except Exception:
                pass
            if getattr(self, "language", "it") == "en":
                self.probable_lan_vendor_count.set(
                    "Count: 0 | LAN visibility: VERY LOW - no DATA/DS frames"
                )
            else:
                self.probable_lan_vendor_count.set(
                    "Numero: 0 | VISIBILITA' LAN: MOLTO BASSA - nessun frame DATA/DS"
                )
        elif not merged and _endpoint_hits == 0 and _vis:
            if getattr(self, "language", "it") == "en":
                self.probable_lan_vendor_count.set(
                    f"Count: 0 | LAN visibility: {_vis} - no DS endpoint observed"
                )
            else:
                self.probable_lan_vendor_count.set(
                    f"Numero: 0 | VISIBILITA' LAN: {_vis} - nessun endpoint DS osservato"
                )
        else:
            # La lista è univoca per MAC: un dispositivo già trovato non viene
            # mostrato una seconda volta; si aggiorna soltanto la provenienza.
            total_visible = len(self.lan_vendor_tree.get_children())
            self.probable_lan_vendor_count.set(f"{label}: {total_visible}")

        self.logmsg(
            (
                f"LAN: {len(merged)} candidati visibili su tutta la scala; esclusa solo infrastruttura radio ({len(hard_excluded_macs)} MAC)."
                if getattr(self,"language","it")!="en" else
                f"LAN: {len(merged)} candidates visible across the full confidence scale; only radio infrastructure excluded ({len(hard_excluded_macs)} MACs)."
            )
        )
        try:
            self._network_graph_snapshot_current(None, "LAN passive/active update")
        except Exception:
            pass


    def _active_lan_gateway_info(self, iface):
        """
        Identifica il gateway predefinito della rete locale del PC e prova a
        risolverne il MAC. Il risultato indica il router/gateway che instrada
        il traffico del PC sulla rete corrente.
        """
        info = {"ip":"", "mac":"", "interface":iface or ""}
        try:
            r = run(["ip","-4","route","show","default"], timeout=5)
            for line in (r.stdout or "").splitlines():
                m = re.search(r"\bdefault\s+via\s+(\d+\.\d+\.\d+\.\d+)\s+dev\s+(\S+)", line)
                if not m:
                    continue
                gw_ip, gw_if = m.group(1), m.group(2)
                if iface and gw_if != iface:
                    continue
                info["ip"] = gw_ip
                info["interface"] = gw_if
                break

            gw_ip = info.get("ip","")
            gw_if = info.get("interface","") or iface
            if not gw_ip:
                return info

            # Stimola ARP/ND IPv4 in modo innocuo se la voce neighbor non è ancora presente.
            try:
                subprocess.run(
                    ["ping","-c","1","-W","1","-I",gw_if,gw_ip],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=2,
                    check=False
                )
            except Exception:
                pass

            r = run(["ip","neigh","show",gw_ip,"dev",gw_if], timeout=5)
            m = re.search(
                r"\blladdr\s+((?:[0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2})\b",
                r.stdout or ""
            )
            if m:
                info["mac"] = m.group(1).lower()
        except Exception:
            pass
        return info

    def _active_lan_default_network(self):
        """Restituisce (interfaccia, IPv4, rete CIDR) usata dalla route predefinita."""
        iface = ""
        src_ip = ""

        # Route effettivamente usata per Internet: evita di scegliere la scheda monitor.
        r = run(["ip","-4","route","get","1.1.1.1"], timeout=4)
        line = (r.stdout or "").strip().splitlines()
        line = line[0] if line else ""
        m = re.search(r"\bdev\s+(\S+)", line)
        if m:
            iface = m.group(1)
        m = re.search(r"\bsrc\s+(\d+\.\d+\.\d+\.\d+)", line)
        if m:
            src_ip = m.group(1)

        if not iface:
            r = run(["ip","-4","route","show","default"], timeout=4)
            m = re.search(r"\bdev\s+(\S+)", r.stdout or "")
            if m:
                iface = m.group(1)

        if not iface:
            raise RuntimeError(
                "No active IPv4 network interface with a default route was found."
                if getattr(self,"language","it")=="en" else
                "Nessuna interfaccia IPv4 attiva con route predefinita trovata."
            )

        r = run(["ip","-o","-4","addr","show","dev",iface,"scope","global"], timeout=4)
        addr_line = (r.stdout or "").strip().splitlines()
        if not addr_line:
            raise RuntimeError(
                f"No IPv4 address is assigned to {iface}."
                if getattr(self,"language","it")=="en" else
                f"Nessun indirizzo IPv4 assegnato a {iface}."
            )

        m = re.search(r"\binet\s+(\d+\.\d+\.\d+\.\d+)/(\d+)", addr_line[0])
        if not m:
            raise RuntimeError("Unable to determine the local IPv4 subnet.")
        ip_s = src_ip or m.group(1)
        prefix = int(m.group(2))
        net = ipaddress.ip_network(f"{m.group(1)}/{prefix}", strict=False)

        # Evita scansioni accidentali di reti enormi: massimo 1024 indirizzi.
        if net.num_addresses > 1024:
            net = ipaddress.ip_network(f"{ip_s}/24", strict=False)
            self.logmsg(
                (f"ACTIVE LAN: network larger than 1024 addresses; scan limited to {net}.")
                if getattr(self,"language","it")=="en" else
                (f"LAN ATTIVA: rete oltre 1024 indirizzi; scansione limitata a {net}.")
            )
        return iface, ip_s, net


    def _active_lan_interface_is_wifi(self, iface):
        """Return True when iface is a Wi-Fi interface."""
        try:
            if Path(f"/sys/class/net/{iface}/wireless").exists():
                return True
        except Exception:
            pass

        try:
            r = run(["iw", "dev", iface, "info"], timeout=4)
            out = ((r.stdout or "") + "\n" + (r.stderr or "")).lower()
            if "interface " in out and ("type managed" in out or "wiphy " in out):
                return True
        except Exception:
            pass
        return False


    def _active_lan_capture_network_match(self, iface):
        """Return (match, connected_bssid).

        match=True  : managed Wi-Fi interface is connected to the captured BSSID.
        match=False : managed Wi-Fi interface is connected to a DIFFERENT BSSID.
        match=None  : interface is not a managed Wi-Fi link / cannot be determined.

        This guard prevents ACTIVE-LAN discovery from contaminating the table with
        hosts belonging to another network used by the PC for Internet access.
        """
        target = (self.bssid.get() or "").strip().lower()
        if not MAC_FULL.match(target):
            return None, ""

        try:
            r = run(["iw", "dev", iface, "link"], timeout=4)
            out = (r.stdout or "") + "\n" + (r.stderr or "")
        except Exception:
            return None, ""

        m = re.search(
            r"Connected\s+to\s+((?:[0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2})",
            out,
            re.I
        )
        if not m:
            return None, ""

        connected = m.group(1).lower()
        return connected == target, connected


    def _active_lan_parse_arp_scan(self, output):
        found = {}
        for line in (output or "").splitlines():
            m = re.match(
                r"^\s*(\d+\.\d+\.\d+\.\d+)\s+"
                r"((?:[0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2})"
                r"(?:\s+(.*?))?\s*$", line
            )
            if not m:
                continue
            ip_s, mac, vendor = m.group(1), m.group(2).lower(), (m.group(3) or "").strip()
            if MAC_FULL.match(mac) and not self.is_multicast_or_broadcast(mac):
                found[mac] = {"ip":ip_s, "vendor":vendor}
        return found


    def _active_lan_parse_nmap(self, output):
        found = {}
        current_ip = ""
        for line in (output or "").splitlines():
            m = re.search(r"Nmap scan report for (?:.*\()?(\d+\.\d+\.\d+\.\d+)\)?", line)
            if m:
                current_ip = m.group(1)
                continue
            m = re.search(
                r"MAC Address:\s*((?:[0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2})(?:\s+\((.*?)\))?",
                line
            )
            if m and current_ip:
                mac = m.group(1).lower()
                vendor = (m.group(2) or "").strip()
                if MAC_FULL.match(mac) and not self.is_multicast_or_broadcast(mac):
                    found[mac] = {"ip":current_ip, "vendor":vendor}
        return found


    def _active_lan_ping_neigh_fallback(self, iface, net):
        """Fallback senza arp-scan/nmap: ping paralleli per popolare la neighbor table."""
        hosts = [str(x) for x in net.hosts()]
        # La rete è già limitata a <=1024 indirizzi.
        def probe(ip_s):
            try:
                subprocess.run(
                    ["ping","-c","1","-W","1","-I",iface,ip_s],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=2,
                    check=False
                )
            except Exception:
                pass
            return ip_s

        with ThreadPoolExecutor(max_workers=min(64, max(1,len(hosts)))) as ex:
            futures = [ex.submit(probe, ip_s) for ip_s in hosts]
            for _ in as_completed(futures):
                pass

        found = {}
        r = run(["ip","neigh","show","dev",iface], timeout=5)
        for line in (r.stdout or "").splitlines():
            # 192.168.1.10 lladdr aa:bb:cc:dd:ee:ff REACHABLE
            m = re.match(
                r"^\s*(\d+\.\d+\.\d+\.\d+)\s+.*?\blladdr\s+"
                r"((?:[0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2})\b",
                line
            )
            if not m:
                continue
            ip_s, mac = m.group(1), m.group(2).lower()
            if MAC_FULL.match(mac) and not self.is_multicast_or_broadcast(mac):
                found[mac] = {"ip":ip_s, "vendor":""}
        return found


    def start_active_lan_scan(self):
        """
        Scansione esplicita della LAN IP a cui è connesso il PC.
        È avviata automaticamente insieme alla cattura passiva 802.11 e genera traffico di discovery.
        """
        if getattr(self, "active_lan_scan_running", False):
            return

        self.active_lan_scan_running = True
        try:
            self.active_lan_scan_button.configure(state="disabled")
        except Exception:
            pass

        self.logmsg(
            "ACTIVE LAN: starting local-network discovery..."
            if getattr(self,"language","it")=="en" else
            "LAN ATTIVA: avvio rilevamento della rete locale..."
        )

        threading.Thread(target=self._active_lan_scan_worker, daemon=True).start()


    def _active_lan_scan_worker(self):
        is_en = getattr(self,"language","it")=="en"
        try:
            iface, local_ip, net = self._active_lan_default_network()
            gateway_info = self._active_lan_gateway_info(iface)
            self.lan_gateway_info = dict(gateway_info)
            gateway_ip = str(gateway_info.get("ip","")).strip()
            gateway_mac = str(gateway_info.get("mac","")).strip().lower()

            # IMPORTANT: the active scan uses the PC's default-route network.
            # If that Wi-Fi interface is associated to another BSSID, its hosts
            # have NOTHING to do with the captured network and must not enter
            # the LAN table.
            network_match, connected_bssid = self._active_lan_capture_network_match(iface)
            target_bssid = (self.bssid.get() or "").strip().lower()
            default_iface_is_wifi = self._active_lan_interface_is_wifi(iface)

            # CROSS-NETWORK GUARD:
            # If the PC reaches the Internet through a Wi-Fi interface, ACTIVE-LAN
            # may only be used when that SAME interface is positively confirmed on
            # the BSSID currently being captured.
            #
            # - False  => definitely another Wi-Fi network: suppress.
            # - None   => BSSID could not be read: suppress as well (fail closed),
            #            otherwise arp-scan/nmap would import the PC's Internet LAN.
            suppress_foreign_wifi = bool(
                default_iface_is_wifi and network_match is not True
            )

            if suppress_foreign_wifi:
                self.active_lan_results = {}
                self.lan_gateway_info = {}
                self.active_lan_scan_info = {
                    "interface": iface,
                    "local_ip": local_ip,
                    "subnet": str(net),
                    "method": (
                        "SUPPRESSED-BSSID-MISMATCH"
                        if network_match is False
                        else "SUPPRESSED-WIFI-BSSID-UNVERIFIED"
                    ),
                    "count": 0,
                    "gateway_ip": "",
                    "gateway_mac": "",
                    "connected_bssid": connected_bssid,
                    "target_bssid": target_bssid,
                }

                def finish_mismatch():
                    # Remove any gateway/active rows left from the PC's previous
                    # Internet-side discovery before rebuilding the LAN table.
                    for _mac in list(getattr(self, "lan_persistent_rows", {}) or {}):
                        _det = (getattr(self, "lan_persistent_details", {}) or {}).get(_mac, {}) or {}
                        _src = str(_det.get("source", "")).upper()
                        if _src in ("DEFAULT-GATEWAY", "ACTIVE-LAN", "ACTIVE-LAN-LOW-TRAFFIC"):
                            self.lan_persistent_rows.pop(_mac, None)
                            self.lan_persistent_details.pop(_mac, None)
                            try:
                                self.lan_candidate_details.pop(_mac, None)
                            except Exception:
                                pass

                    self.update_probable_lan_vendors(
                        list(getattr(self, "live_mac_rows", {}).values())
                    )
                    if network_match is False:
                        msg = (
                            f"ACTIVE LAN ignored: PC Internet Wi-Fi is on BSSID {connected_bssid}, "
                            f"capture target is {target_bssid}."
                            if is_en else
                            f"LAN ATTIVA ignorata: il Wi-Fi Internet del PC è sul BSSID {connected_bssid}, "
                            f"la cattura riguarda {target_bssid}."
                        )
                    else:
                        msg = (
                            f"ACTIVE LAN ignored: {iface} is the PC Internet Wi-Fi interface, "
                            "but its connected BSSID could not be verified against the capture target."
                            if is_en else
                            f"LAN ATTIVA ignorata: {iface} è l'interfaccia Wi-Fi Internet del PC, "
                            "ma non è stato possibile verificare che il suo BSSID coincida con quello catturato."
                        )
                    self.logmsg(msg)
                    self.active_lan_scan_running = False
                    try:
                        self.active_lan_scan_button.configure(state="normal")
                    except Exception:
                        pass

                self.root.after(0, finish_mismatch)
                return

            self.logmsg(
                f"ACTIVE LAN: interface={iface}, local IP={local_ip}, subnet={net}"
                if is_en else
                f"LAN ATTIVA: interfaccia={iface}, IP locale={local_ip}, sottorete={net}"
            )

            found = {}
            method = ""

            arp_scan = shutil.which("arp-scan")
            nmap = shutil.which("nmap")

            if arp_scan:
                method = "arp-scan"
                r = run(
                    [arp_scan, f"--interface={iface}", "--localnet", "--retry=2", "--timeout=500"],
                    timeout=90
                )
                found = self._active_lan_parse_arp_scan(r.stdout)
                if not found and r.stderr:
                    self.logmsg(f"arp-scan: {r.stderr.strip()[:300]}")

            if not found and nmap:
                method = "nmap -sn"
                r = run([nmap, "-sn", "-PR", "-n", str(net)], timeout=120)
                found = self._active_lan_parse_nmap(r.stdout)
                if not found and r.stderr:
                    self.logmsg(f"nmap: {r.stderr.strip()[:300]}")

            if not found:
                method = "ping + ip neigh"
                found = self._active_lan_ping_neigh_fallback(iface, net)

            # Il gateway deve essere mostrato anche se gli altri tool non lo hanno
            # restituito: se il kernel ne conosce MAC/IP lo aggiungiamo esplicitamente.
            if gateway_mac and MAC_FULL.match(gateway_mac) and not self.is_multicast_or_broadcast(gateway_mac):
                found.setdefault(gateway_mac, {"ip":gateway_ip, "vendor":""})

            # Rimuove il PC stesso e il gateway/AP se riconoscibile solo quando
            # corrispondono esattamente al MAC della nostra interfaccia o all'IP locale.
            own_mac = ""
            try:
                own_mac = Path(f"/sys/class/net/{iface}/address").read_text().strip().lower()
            except Exception:
                pass

            cache = load_vendor_cache()
            results = {}
            radio_known = set(getattr(self, "wifi_radio_macs_session", set()) or set())
            for mac, rec in sorted(found.items()):
                ip_s = str(rec.get("ip","")).strip()
                if mac == own_mac or ip_s == local_ip:
                    continue

                # Il gateway di sistema ha precedenza: non deve sparire dalla tabella
                # LAN solo perché il suo MAC è comparso accidentalmente nella cache
                # radio del PCAP (bridge/AP possono rendere ambigui alcuni indirizzi).
                is_gateway = bool(
                    (gateway_mac and mac == gateway_mac) or
                    (gateway_ip and ip_s == gateway_ip)
                )

                # Discovery IP può trovare anche normali client Wi-Fi.
                # Manteniamo l'esclusione radio, MA NON per il gateway predefinito,
                # che è identificato direttamente dalla route del sistema.
                if mac in radio_known and not is_gateway:
                    continue

                vendor = str(rec.get("vendor","")).strip()
                # arp-scan/nmap possono restituire stringhe placeholder ("Unknown",
                # "Sconosciuto", ecc.). Non considerarle un vendor valido, altrimenti
                # bloccano i fallback OUI e fanno perdere NETGEAR/Raspberry Pi.
                if vendor.lower() in (
                    "unknown", "sconosciuto", "(unknown)", "unknown vendor",
                    "vendor unknown", "n/a", "none", "-"
                ):
                    vendor = ""
                if not vendor:
                    vendor = str(cache.get(mac, "") or "").strip()
                    if vendor.lower() in (
                        "unknown", "sconosciuto", "(unknown)", "unknown vendor",
                        "vendor unknown", "n/a", "none", "-"
                    ):
                        vendor = ""
                if not vendor:
                    try:
                        oui_cache = self._load_tshark_manuf_cache()
                        oui = ":".join(mac.upper().split(":")[:3])
                        rv = oui_cache.get(oui)
                        if rv:
                            short_name, long_name = rv
                            vendor = (long_name or short_name or "").strip()
                    except Exception:
                        pass
                if not vendor:
                    # Ultimo fallback OUI online, limitato alla discovery attiva.
                    # Serve soprattutto per embedded a basso traffico che altrimenti
                    # resterebbero "Sconosciuto" e non potrebbero essere riconosciuti.
                    try:
                        _resolved_vendor = lookup_vendor(mac, cache)
                        if _resolved_vendor not in ("Sconosciuto", "Unknown", ""):
                            vendor = _resolved_vendor
                    except Exception:
                        pass
                if not vendor:
                    vendor = "Unknown" if is_en else "Sconosciuto"

                # Identificazione del router/gateway principale della rete del PC.
                # is_gateway è già stato calcolato PRIMA del filtro radio:
                # la route predefinita è una prova più forte dell'ambiguità radio.

                if is_gateway:
                    score = 100
                    level = "PRIMARY GATEWAY" if is_en else "GATEWAY PRINCIPALE"
                    role = "ROUTER"
                    evidence = (
                        f"DEFAULT-GATEWAY 100/100 | IP {ip_s} | interface={iface} | method={method}"
                    )
                else:
                    score = 90
                    level = "LOCAL ACTIVE" if is_en else "ATTIVO LOCALE"
                    role = "LAN"
                    evidence = (
                        f"ACTIVE-LAN 90/100 | IP {ip_s} | method={method}"
                    )
                if is_gateway:
                    notes = (
                        f"This host is the IPv4 default gateway used by the PC on interface {iface}. "
                        "It is therefore the local router that governs traffic leaving this subnet. "
                        "The Wi-Fi BSSID MAC may be different from this LAN-side gateway MAC."
                        if is_en else
                        f"Questo host è il gateway IPv4 predefinito usato dal PC sull'interfaccia {iface}. "
                        "È quindi il router locale che governa il traffico in uscita da questa sottorete. "
                        "Il MAC del BSSID Wi-Fi può essere diverso dal MAC lato LAN del gateway."
                    )
                else:
                    notes = (
                        f"Host actively discovered on local subnet {net} through {iface}. "
                        "This confirms presence on the same local IP network, but by itself does not prove "
                        "that the device is physically connected by Ethernet rather than Wi-Fi."
                        if is_en else
                        f"Host rilevato attivamente nella sottorete locale {net} tramite {iface}. "
                        "Conferma la presenza nella stessa rete IP locale, ma da sola non dimostra "
                        "che il dispositivo sia collegato fisicamente via Ethernet anziché Wi-Fi."
                    )
                results[mac] = {
                    "display": (vendor, mac, f"{score}/100", level, role),
                    "details": {
                        "mac":mac,
                        "vendor":vendor,
                        "score":score,
                        "level":level,
                        "evidence":evidence,
                        "notes":notes,
                        "ip":ip_s,
                        "source":"DEFAULT-GATEWAY" if is_gateway else "ACTIVE-LAN",
                        "role":role,
                        "is_gateway":is_gateway,
                        "gateway_ip":gateway_ip,
                        "gateway_mac":gateway_mac,
                        "reasons":(
                            [
                                (
                                    f"System default route points to {gateway_ip} on interface {iface}."
                                    if is_en else
                                    f"La route predefinita del sistema punta a {gateway_ip} sull'interfaccia {iface}."
                                ),
                                (
                                    f"Gateway MAC resolved as {gateway_mac or mac}."
                                    if is_en else
                                    f"MAC del gateway risolto come {gateway_mac or mac}."
                                ),
                                (
                                    "This identifies the local router/default gateway; an upstream ISP router may still exist."
                                    if is_en else
                                    "Questo identifica il router/gateway locale; può comunque esistere un ulteriore router a monte dell'operatore."
                                ),
                            ]
                            if is_gateway else
                            [
                            (
                                f"Host actively responded/appeared in local neighbor discovery at IP {ip_s}"
                                if is_en else
                                f"Host rilevato dalla discovery locale attiva all'IP {ip_s}"
                            ),
                            (
                                f"Discovery interface: {iface}; subnet: {net}; method: {method}"
                                if is_en else
                                f"Interfaccia di discovery: {iface}; sottorete: {net}; metodo: {method}"
                            ),
                            (
                                "Known Wi-Fi clients are excluded from the LAN candidate table."
                                if is_en else
                                "I client Wi-Fi già noti vengono esclusi dalla tabella dei candidati LAN."
                            ),
                            ]
                        ),
                    },
                }

            self.active_lan_results = results
            self.active_lan_scan_info = {
                "interface":iface, "local_ip":local_ip, "subnet":str(net),
                "method":method, "count":len(results),
                "gateway_ip":gateway_ip, "gateway_mac":gateway_mac,
                "connected_bssid": connected_bssid,
                "target_bssid": target_bssid,
            }

            def finish_ok():
                # Forza il merge dei risultati attivi con quelli passivi già presenti.
                rows = list(getattr(self,"live_mac_rows",{}).values())
                self.update_probable_lan_vendors(rows)
                try:
                    self._network_graph_snapshot_current(None, "active LAN scan complete")
                except Exception:
                    pass
                self.logmsg(
                    f"ACTIVE LAN: {len(results)} local hosts detected with {method}."
                    if is_en else
                    f"LAN ATTIVA: {len(results)} host locali rilevati con {method}."
                )
                self.active_lan_scan_running = False
                try:
                    self.active_lan_scan_button.configure(state="normal")
                except Exception:
                    pass

            self.root.after(0, finish_ok)

        except Exception as e:
            def finish_err(err=str(e)):
                self.logmsg(("ACTIVE LAN error: " if is_en else "Errore LAN ATTIVA: ") + err)
                self.active_lan_scan_running = False
                try:
                    self.active_lan_scan_button.configure(state="normal")
                except Exception:
                    pass
                try:
                    messagebox.showwarning(
                        "ACTIVE LAN" if is_en else "LAN ATTIVA",
                        err
                    )
                except Exception:
                    pass
            self.root.after(0, finish_err)


    def _on_lan_row_click(self, event=None):
        if not hasattr(self,"lan_vendor_tree"):
            return
        try:
            rowid=self.lan_vendor_tree.identify_row(event.y) if event is not None else ""
        except Exception:
            rowid=""
        if not rowid:
            sel=self.lan_vendor_tree.selection()
            rowid=sel[0] if sel else ""
        if not rowid:
            return

        vals=self.lan_vendor_tree.item(rowid,"values")
        if len(vals)<5:
            return
        # Nella tabella LAN l'ordine visuale è:
        # VENDITORE | RUOLO | PROBABILITA' | SCORE | MACS
        # Il MAC corretto è quindi l'indice 4.
        mac=str(vals[4]).lower()
        self._show_lan_detail(mac)



    def _prepare_modal_popup(self, win):
        """Rende il popup figlio/modale della GUI mantenendo la root visibile sotto."""
        try:
            win.transient(self.root)
        except Exception:
            pass
        try:
            win.grab_set()
        except Exception:
            pass
        try:
            # Mantiene la root fullscreen e visibile sotto il popup.
            if bool(self.root.attributes("-fullscreen")):
                self.root.attributes("-fullscreen", True)
        except Exception:
            pass
        try:
            self.root.lift()
        except Exception:
            pass
        try:
            win.lift()
        except Exception:
            pass

        def _restore_root(_event=None):
            try:
                win.grab_release()
            except Exception:
                pass
            try:
                if self.root.winfo_exists():
                    self.root.lift()
                    self.root.focus_force()
            except Exception:
                pass

        try:
            win.bind("<Destroy>", _restore_root, add="+")
        except Exception:
            pass


    def _create_inapp_detail_popup(self, title, width=760, height=600):
        """
        Crea un pannello modale INTERNO alla GUI.
        Non usa tk.Toplevel: il window manager non può quindi mostrare
        pannelli, icone o desktop del sistema operativo dietro al dettaglio.
        """
        dark=bool(getattr(self,"night_mode",False))
        bg="#12171B" if dark else "#ECEFF1"
        panel="#1A2126" if dark else "#FFFFFF"
        border="#232C31" if dark else "#9AA4AA"
        fg="#E7ECEF" if dark else "#111111"

        # Il frame viene creato ma NON ancora posizionato: viene mostrato
        # solo dopo aver costruito tutto il contenuto.
        popup=tk.Frame(
            self.root,
            bg=bg,
            highlightthickness=(1 if dark else 2),
            highlightbackground=border,
            highlightcolor=border,
            bd=0
        )
        popup._popup_width=int(width)
        popup._popup_height=int(height)

        # Barra titolo interna, così non serve alcuna decorazione del WM.
        titlebar=tk.Frame(popup,bg=panel,height=38)
        titlebar.pack(fill="x")
        titlebar.pack_propagate(False)

        title_label=tk.Label(
            titlebar,
            text=title,
            bg=panel,
            fg=fg,
            font=("TkDefaultFont",11,"bold"),
            anchor="w",
            padx=12
        )
        title_label.pack(side="left",fill="both",expand=True)

        # Trascinamento del pannello interno tramite barra del titolo.
        popup._drag_start_x = 0
        popup._drag_start_y = 0
        popup._drag_orig_x = 0
        popup._drag_orig_y = 0

        def _drag_start(event):
            try:
                popup._drag_start_x = int(event.x_root)
                popup._drag_start_y = int(event.y_root)
                info = popup.place_info()
                popup._drag_orig_x = int(float(info.get("x", popup.winfo_x())))
                popup._drag_orig_y = int(float(info.get("y", popup.winfo_y())))
                popup.lift()
            except Exception:
                pass

        def _drag_move(event):
            try:
                dx = int(event.x_root) - int(popup._drag_start_x)
                dy = int(event.y_root) - int(popup._drag_start_y)

                rw = max(1, int(self.root.winfo_width()))
                rh = max(1, int(self.root.winfo_height()))
                pw = max(1, int(popup.winfo_width()))
                ph = max(1, int(popup.winfo_height()))

                nx = popup._drag_orig_x + dx
                ny = popup._drag_orig_y + dy

                # Mantieni sempre il pannello completamente dentro la GUI.
                nx = max(0, min(nx, max(0, rw - pw)))
                ny = max(0, min(ny, max(0, rh - ph)))

                popup.place_configure(x=nx, y=ny)
                popup.lift()
            except Exception:
                pass

        for _drag_widget in (titlebar, title_label):
            _drag_widget.bind("<ButtonPress-1>", _drag_start)
            _drag_widget.bind("<B1-Motion>", _drag_move)
            _drag_widget.configure(cursor="fleur")

        def close_popup():
            try:
                popup.grab_release()
            except Exception:
                pass
            try:
                popup.destroy()
            except Exception:
                pass
            try:
                self.root.focus_force()
            except Exception:
                pass

        close_x=tk.Button(
            titlebar,
            text="✕",
            command=close_popup,
            bg=panel,
            fg=fg,
            activebackground=border,
            activeforeground=fg,
            relief="flat",
            borderwidth=0,
            font=("TkDefaultFont",12,"bold"),
            width=3,
            cursor="hand2"
        )
        close_x.pack(side="right",fill="y")

        popup._close_popup=close_popup
        popup.bind("<Escape>",lambda _e: close_popup())
        return popup

    def _show_inapp_detail_popup(self, popup):
        """Mostra il pannello già completamente costruito al centro della GUI."""
        try:
            self.root.update_idletasks()
            rw=max(800,int(self.root.winfo_width()))
            rh=max(600,int(self.root.winfo_height()))
            w=min(int(getattr(popup,"_popup_width",760)), max(560,rw-80))
            h=min(int(getattr(popup,"_popup_height",600)), max(420,rh-80))
            x=max(0,(rw-w)//2)
            y=max(0,(rh-h)//2)
            popup.place(x=x,y=y,width=w,height=h)
            popup.lift()
            popup.grab_set()
            popup.focus_set()
        except Exception:
            try:
                popup.place(relx=0.5,rely=0.5,anchor="center")
                popup.lift()
                popup.grab_set()
            except Exception:
                pass

    def _build_score_panel(self, win, score, level, kind="LAN"):
        """Pannello score grafico comune a LAN e telecamere."""
        is_en=getattr(self,"language","it")=="en"
        dark=bool(getattr(self,"night_mode",False))
        bg="#12171B" if dark else "#ECEFF1"
        fg="#E7ECEF" if dark else "#111111"
        muted="#C8D1D6" if dark else "#333333"
        meter_bg="#2A3238" if dark else "#D9D9D9"
        meter_fill="#5B6F7A" if dark else "#607D8B"
        tick_fg="#8E9AA1" if dark else "#666666"

        wrap=tk.Frame(win,bg=bg)
        wrap.pack(fill="x",padx=14,pady=(12,4))

        title_text=("CAMERA SCORE" if kind=="CAMERA" else "LAN SCORE")
        tk.Label(
            wrap,text=title_text,
            font=("TkDefaultFont",11,"bold"),
            bg=bg,fg=fg
        ).pack(anchor="w")

        line=tk.Frame(wrap,bg=bg)
        line.pack(fill="x",pady=(4,0))

        tk.Label(
            line,text=f"{int(score)} / 100",
            font=("TkDefaultFont",14,"bold"),
            width=9,anchor="w",
            bg=bg,fg=fg
        ).pack(side="left")

        prob_label=("LIKELIHOOD: " if is_en else "PROBABILITA': ")
        tk.Label(
            line,text=prob_label+str(level),
            font=("TkDefaultFont",10,"bold"),
            anchor="w",bg=bg,fg=muted
        ).pack(side="left",padx=(8,0))

        meter=tk.Canvas(
            wrap,height=20,bg=bg,
            highlightthickness=0,borderwidth=0
        )
        meter.pack(fill="x",pady=(6,2))

        def draw(_event=None):
            try:
                meter.delete("all")
                w=max(10,meter.winfo_width())
                h=max(8,meter.winfo_height())
                pad=2
                meter.create_rectangle(
                    pad,pad,w-pad,h-pad,
                    fill=meter_bg,outline=""
                )
                frac=max(0.0,min(1.0,float(score)/100.0))
                fw=pad+(w-2*pad)*frac
                if fw>pad:
                    meter.create_rectangle(
                        pad,pad,fw,h-pad,
                        fill=meter_fill,outline=""
                    )
                for pct in (0,25,50,75,100):
                    x=pad+(w-2*pad)*(pct/100.0)
                    meter.create_line(x,h-5,x,h-2,fill=tick_fg)
            except Exception:
                pass

        meter.bind("<Configure>",draw)
        try:
            win.after_idle(draw)
        except Exception:
            pass
        return wrap
    def _show_lan_detail(self, mac):
        mac=str(mac or "").lower()
        detail=(getattr(self,"lan_candidate_details",{}) or {}).get(mac)
        is_en=getattr(self,"language","it")=="en"
        if not detail:
            messagebox.showinfo(
                "LAN-side analysis" if is_en else "Dettagli LAN",
                "Detailed analysis is not available for this device." if is_en
                else "Detailed analysis is not available for this device."
            )
            return

        title="LAN-SIDE DEVICE ANALYSIS" if is_en else "ANALISI DISPOSITIVO LAN"
        win=self._create_inapp_detail_popup(title,760,560)
        self.lan_detail_window=win

        score=int(detail.get("score",0))
        level=self._lan_level_from_score(score)

        self._build_score_panel(win,score,level,kind="LAN")

        if is_en:
            lines=[
                "IDENTITY",
                f"MAC: {detail.get('mac','--')}",
                f"VENDOR: {detail.get('vendor','Unknown')}",
                f"ROLE: {detail.get('role','LAN')}",
                "",
                "LAN SCORE",
                f"{score} / 100",
                f"LIKELIHOOD: {level}",
                "",
                "OBSERVED EVIDENCE",
                self._lan_text_for_language(detail.get("evidence","--")),
                "",
                "CLASSIFICATION RATIONALE",
            ]
        else:
            lines=[
                "IDENTITA'",
                f"MAC: {detail.get('mac','--')}",
                f"VENDITORE: {detail.get('vendor','Sconosciuto')}",
                f"RUOLO: {detail.get('role','LAN')}",
                "",
                "LAN SCORE",
                f"{score} / 100",
                f"PROBABILITA': {level}",
                "",
                "EVIDENZE OSSERVATE",
                self._lan_text_for_language(detail.get("evidence","--")),
                "",
                "MOTIVAZIONI DELLA CLASSIFICAZIONE LAN",
            ]

        # Rebuild rationale in the CURRENT GUI language. This prevents
        # Italian cached strings from appearing after switching to English.
        current_reasons=self._lan_reasons_from_evidence(
            detail.get("evidence",""),
            detail.get("notes","")
        )
        for reason in current_reasons or []:
            lines.append("• "+self._lan_text_for_language(reason))

        if detail.get("is_gateway"):
            lines.append(
                "• System default route identifies this host as the router/default gateway for the PC."
                if is_en else
                "• La route predefinita del sistema identifica questo host come router/gateway del PC."
            )
            lines.append(
                "• The Wi-Fi BSSID MAC can legitimately differ from this gateway MAC."
                if is_en else
                "• Il MAC del BSSID Wi-Fi può legittimamente essere diverso dal MAC del gateway."
            )

        lines += [
            "",
            "TECHNICAL NOTE" if is_en else "NOTA TECNICA",
            (
                "The classification is based on observable IEEE 802.11 header fields and indicates an endpoint on the "
                "Distribution System (DS) side. It does not, by itself, prove that the device is physically connected "
                "by Ethernet cable."
                if is_en else
                "La classificazione si basa sugli header 802.11 osservabili e indica un endpoint lato "
                "Distribution System. Da sola non dimostra che il dispositivo sia fisicamente collegato "
                "con un cavo Ethernet."
            )
        ]

        body_frame=tk.Frame(win,bd=0,highlightthickness=0)
        body_frame.pack(fill="both",expand=True,padx=10,pady=(10,5))
        body_frame.columnconfigure(0,weight=1)
        body_frame.rowconfigure(0,weight=1)

        body=tk.Text(
            body_frame,wrap="word",font=("TkDefaultFont",11),
            padx=16,pady=14,borderwidth=0
        )
        body.grid(row=0,column=0,sticky="nsew")

        body_y=ttk.Scrollbar(
            body_frame,orient="vertical",command=body.yview
        )
        body_y.grid(row=0,column=1,sticky="ns")
        body.configure(yscrollcommand=body_y.set)

        body.insert("1.0","\n".join(lines))
        body.configure(state="disabled")
        self._enable_detail_text_copy(body)

        close=tk.Button(
            win,
            text=("CLOSE" if is_en else "CHIUDI"),
            command=win._close_popup,
            padx=18,pady=5
        )
        close.pack(pady=(3,10))
        win.bind("<Escape>",lambda _e: win._close_popup())

        # Riusa il sistema dark già collaudato per i dettagli telecamera.
        try:
            self._force_camera_detail_dark_theme(win)
            win.update_idletasks()
            win.update()
            self._force_camera_detail_dark_theme(win)
            win.update_idletasks()
        except Exception:
            pass
        self._show_inapp_detail_popup(win)

    def _refresh_result_counters(self):
        """Aggiorna il contatore visivo della tabella delle possibili telecamere."""
        try:
            ncam = len(self.camera_tree.get_children())
        except Exception:
            ncam = 0
        try:
            self.camera_number_text.set(
                ("Count: " if getattr(self, "language", "it") == "en" else "Numero: ") + str(ncam)
            )
        except Exception:
            pass


    def fill_results(self,rows):
        for x in self.res_tree.get_children():
            self.res_tree.delete(x)

        normalized=[]
        for row in rows:
            try:
                if len(row) >= 5:
                    mac,vendor,cls,evidence,notes = row[:5]
                elif len(row) == 4:
                    mac,vendor,cls,notes = row
                    evidence = ""
                else:
                    continue
                normalized.append((mac,vendor,cls,evidence,notes))
            except Exception as e:
                self.logmsg(f"Errore normalizzazione riga MAC {row}: {e}")

        current_source = str(
            getattr(self, "_passive_current_source_label", "") or ""
        ).strip()
        for row in normalized:
            self.res_tree.insert(
                "","end",
                values=tuple(self._mac_row_for_language(row)) + (current_source,)
            )

        wifi_clients=sum(1 for r in normalized if r[2] == "Wi-Fi ASSOCIATO")
        lan_candidates=sum(1 for r in normalized if r[2] == "LAN CANDIDATO")
        other=sum(1 for r in normalized if r[2] == "ALTRO/INCERTO")

        if self.language == "en":
            self.lan_count.set(f"LAN-side candidates (not confirmed): {lan_candidates}")
            self.other_count.set(f"Other / uncertain: {other}")
        else:
            self.lan_count.set(f"LAN candidati (non certi): {lan_candidates}")
            self.other_count.set(f"Altro/incerto: {other}")

        self.update_probable_lan_vendors(normalized)
        self.logmsg(f"Tabella MAC aggiornata: {len(normalized)} righe")
        try:
            self._refresh_result_counters()
        except Exception:
            pass


    def open_pcap(self):
        """
        Apre il PCAP in Wireshark con privilegi amministrativi.
        Preferisce pkexec; se non disponibile usa sudo.
        """
        cap=self.capture_file
        if not cap or not Path(cap).exists():
            messagebox.showwarning(
                "PCAP",
                "Nessun file PCAP disponibile da aprire."
            )
            return

        wireshark=shutil.which("wireshark")
        if not wireshark:
            messagebox.showerror(
                "Wireshark",
                "Wireshark non risulta installato o non è nel PATH."
            )
            return

        cap=str(Path(cap).resolve())

        try:
            pkexec=shutil.which("pkexec")
            if pkexec:
                self.logmsg(f"$ pkexec {wireshark} {cap}")
                popen_logged(
                    [pkexec, wireshark, cap],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    start_new_session=True
                )
                self.set_status("Apertura Wireshark con privilegi amministrativi...")
                return

            sudo=shutil.which("sudo")
            if sudo:
                self.logmsg(f"$ sudo -H {wireshark} {cap}")
                popen_logged(
                    [sudo, "-H", wireshark, cap],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    start_new_session=True
                )
                self.set_status("Apertura Wireshark con sudo...")
                return

            messagebox.showerror(
                "Permessi",
                "Non sono disponibili né pkexec né sudo per avviare Wireshark come amministratore."
            )

        except Exception as e:
            self.logmsg(f"Errore apertura Wireshark: {e}")
            messagebox.showerror(
                "Wireshark",
                f"Impossibile aprire il PCAP con privilegi amministrativi:\n{e}"
            )

if __name__=="__main__":
    root=tk.Tk()
    App(root)
    root.mainloop()
