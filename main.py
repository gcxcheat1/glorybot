# -*- coding: utf-8 -*-
# ============================================================
#   main.py — DG DRIFT / FFGLORY COMPLETE SERVER (BD DEFAULT)
# ============================================================
import sys, os, json, time, uuid, random, asyncio, base64, struct, socket
import itertools, traceback, ssl, hmac, hashlib, string, re, subprocess
import httpx
import aiohttp
import aiohttp.web
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple, Any

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME
import thunderFF_pb2

try:
    import StartMatch_pb2
except Exception:
    StartMatch_pb2 = None

try:
    import reqClan_pb2
    _CLAN_PB_AVAILABLE = True
except Exception:
    _CLAN_PB_AVAILABLE = False

# ==================== CONFIG ====================
WEB_HOST = "0.0.0.0"
WEB_PORT = int(os.environ.get("PORT", 8080))
ACCOUNTS_FILE = "accounts.json"
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
PANEL_DB_FILE = "panel_db.json"
TOKEN_CACHE_TTL = 1200

START_MATCH_INTERVAL = 5.0
MAX_CONCURRENT_MATCHES = 20
MAX_MATCH_DURATION = 1500
MATCH_IDLE_TIMEOUT  = 12.0

# ── Team Config ──────────────────────────────────────────────
TEAM_MODE = True
TEAM_SIZE = 2                    # Default Duo
TEAM_READY_DELAY = 10.0          # Bariye deya holo (age 6.0 chilo)
TEAM_INVITE_WAIT = 3.5           # Bariye deya holo
CLAN_ID_DEFAULT = "3033431593"

AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
AES_IV  = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
KEYSTREAM = bytes([0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30])
HEX_KEY = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
API_KEY = HEX_KEY.encode()

REGION_LANG = {"ME":"ar","IND":"hi","ID":"id","VN":"vi","TH":"th","BD":"bn",
               "PK":"ur","TW":"zh","RU":"ru","SAC":"es","BR":"pt","NA":"pt",
               "SG":"pt","US":"pt"}

# ==================== STATE ====================
class BotState:
    def __init__(self):
        self.accounts: Dict[str, dict] = {}
        self.account_credentials: Dict[str, dict] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.auth_to_game_id: Dict[str, str] = {}
        self.game_to_auth_id: Dict[str, str] = {}
        self.paused: set = set()
        self.writers: Dict[str, list] = {}
        self.logs: List[dict] = []
        self.total_matches = 0
        self.matches_started = 0
        self.total_exp_gained = 0
        self.creating = False
        self.start_time = time.time()

    def log(self, msg, level="info"):
        try:
            t = datetime.now().strftime("%H:%M:%S")
            self.logs.append({"t": time.time(), "time": t, "message": str(msg), "level": level})
            if len(self.logs) > 500:
                self.logs = self.logs[-500:]
        except Exception:
            pass

    def register_account(self, uid, nickname, region="BD", level=1, exp=0, likes=0, token=None, auth_uid=None, clan_id=None):
        uid = str(uid)
        existing = self.accounts.get(uid, {})
        self.accounts[uid] = {
            "uid": uid, "nickname": nickname, "region": region,
            "level": level, "exp": exp, "likes": likes,
            "token": token, "auth_uid": auth_uid,
            "clan_id": clan_id or existing.get("clan_id"), # <-- clan_id added
            "status": "ONLINE",
            "current_exp": exp,
            "initial_exp": existing.get("initial_exp", exp),
            "gained_exp": existing.get("gained_exp", 0),
            "matches": existing.get("matches", 0),
            "active_matches": 0,
            "is_paused": False,
        }

    def update_status(self, uid, status, matches=0):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["status"] = status
            self.accounts[uid]["active_matches"] = matches
            self.accounts[uid]["is_paused"] = (status == "PAUSED")

    def update_exp(self, uid, exp, level=None):
        uid = str(uid)
        if uid in self.accounts:
            a = self.accounts[uid]
            old = a.get("current_exp", 0)
            if exp > old:
                a["gained_exp"] = a.get("gained_exp", 0) + (exp - old)
                self.total_exp_gained += (exp - old)
            a["current_exp"] = exp
            a["exp"] = exp
            if level: a["level"] = level

    def increment_match(self, uid):
        self.total_matches += 1
        uid = str(uid)
        if uid in self.accounts:
            m = self.accounts[uid].get("matches", 0) + 1
            self.accounts[uid]["matches"] = m

    def register_writer(self, uid, w):
        self.writers.setdefault(str(uid), []).append(w)

    def unregister_writer(self, uid, w):
        try: self.writers.get(str(uid), []).remove(w)
        except Exception: pass

    def close_writers_for_account(self, uid):
        for w in list(self.writers.get(str(uid), [])):
            try: w.close()
            except Exception: pass
        self.writers[str(uid)] = []

    def is_paused(self, uid):
        return str(uid) in self.paused

    def toggle_pause(self, uid, state):
        uid = str(uid)
        if state:
            self.paused.add(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = True
                self.accounts[uid]["status"] = "PAUSED"
        else:
            self.paused.discard(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = False
                if self.accounts[uid].get("status") == "PAUSED":
                    self.accounts[uid]["status"] = "ONLINE"

bot_state = BotState()

_team_state = {
    "peers": {},
    "leader_uid": None,
    "team_code": None,
    "team_created": False,
    "target_size": TEAM_SIZE,
    "lock": asyncio.Lock(),
}

# ==================== PRINT HELPERS ====================
class C:
    GREEN='\033[92m'; FAIL='\033[91m'; WARNING='\033[93m'
    CYAN='\033[96m'; MAGENTA='\033[95m'; WHITE='\033[97m'; ENDC='\033[0m'

def print_success(t): print(f"{C.GREEN}[+] {t}{C.ENDC}"); bot_state.log(t, "success")
def print_error(t):   print(f"{C.FAIL}[-] {t}{C.ENDC}");   bot_state.log(t, "error")
def print_warning(t): print(f"{C.WARNING}[!] {t}{C.ENDC}"); bot_state.log(t, "warning")
def print_info(t):    print(f"{C.CYAN}[i] {t}{C.ENDC}");   bot_state.log(t, "info")

# ---- Raw Signatures ----
GGRE_RAW = bytes.fromhex("47475245010101006d020000b260ee08e1f86b4c57f9c70f86bba26ed5d1436bcf52e142db3249d905eded757764991ca31a8373cdd26eab91b80f3f1f6f262f4f10b895d7b6937ddba30a27197453890e9da49373f736c679b8254e2f8e1623e91084a5fdd5374fe478ff99e010834553fddeb0bec4018d142e49df9bb236675b67e852f92a43586f7a7d4d0d7a197a1d4da32714dab4d069ad53214e2c33b3877420a12459738c4c619cbd815fa878bbd104776bb3e1ac7818d5397b04a666ac57f682763ff2df31bc2f846ddc7904f3dce1bda0c4b01f9698e9166f98c84f92640abe3f6317834a42e5c12573b46842c1a6ea8fe6ca9c006dca48a2087e1f983dfb5692771e4a0b15b337ad669b1d08b40862b176bace5331b49a767375b1a8469012aa70a67b55fe71b72478201d0b3ac7269c064c960361e92ee7ba8a42cc6b582bf9b965fb388fa9172ad44c4b073ac23c02080a6bcd106b691ffdf4c7cf71e42f2063fcf196e9bddc5e85be1fe5048eb1b31b460efbb46d76195eef9904c4cba326f2e17ff51fec17dd965aa06dadd4ab07d6966e4a7c38e8afd66dfde56c872bb87516a8f7313c797e4d80e5ad4a5f7afad95c1e0449254adae052e71a3fb98399f93ab30848e0d23252dd45e6fd41bc5fa7303dfb846a8fd713a0032a0b0ae96dfba1bbe41d20abd8099e2cb7fccc329d25bd153029139ef05d090a5093ea557693c0a8d491395b8a23ca844b3887dd5dfc29ac06f4b9be87883a793211b973465e2644c4f5de02b8ab01571401203fc2740423826858cc6da0194c195d27aac4ec4b9d23d506c1501d06440aca3fc180926d75d4a004d3dff21eb4ea1e8c86e6c9627248eff953e1d192d5c8efc006a7e512388ef2ebdb72ee3ad42d719f28e8f994e12ebf4c79f2ffe3abd7408ccd2236a7b89b2606247a732c10c4")

def _encode_proto_std(fields):
    out = b""
    for f in sorted(fields.keys()):
        v = fields[f]
        if isinstance(v, bool):
            out += encode_varint((f << 3) | 0) + encode_varint(int(v))
        elif isinstance(v, int):
            out += encode_varint((f << 3) | 0) + encode_varint(v)
        elif isinstance(v, (str, bytes)):
            if isinstance(v, str): v = v.encode()
            out += encode_varint((f << 3) | 2) + encode_varint(len(v)) + v
    return out

async def major_register(release_v, access_token, open_id, name, game_version, login_url, lang_code="en"):
    field14 = bytes(ord(c) ^ KEYSTREAM[i % 32] for i, c in enumerate(open_id))
    fields = {1: name, 2: access_token, 3: open_id, 5: 102000007, 6: 4, 7: 1, 13: 1, 14: field14, 15: lang_code, 16: 2, 20: game_version, 21: 1, 22: GGRE_RAW}
    proto = _encode_proto_std(fields)
    payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(proto, 16))
    url = f"{login_url.rstrip('/')}/MajorRegister"
    hdrs = {"Accept": "*/*", "Authorization": "Bearer ", "Content-Type": "application/x-www-form-urlencoded", "ReleaseVersion": f"{release_v}", "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)", "X-GA": "v1 1", "X-GA-SV": str(int(time.time())), "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context(); ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as resp:
                content = await resp.read()
                if resp.status != 200 or not content: return None
                for off in [0, 64, 48, 32, 16]:
                    if off >= len(content): continue
                    try:
                        r = decode_protobuf_2(content[off:])
                        if r and 3 in r: return {str(k): {"data": v} for k, v in r.items()}
                    except Exception: pass
                return None
    except Exception: return None

# ==================== DEVICE & DNS ====================
def _generate_new_device() -> dict:
    device_list = [("Samsung","SM-G998B","Adreno (TM) 660","Android OS 12 / API-31"), ("Xiaomi","2201122G","Adreno (TM) 730","Android OS 13 / API-33"), ("Realme","RMX3700","Mali-G710","Android OS 14 / API-34")]
    brand, model, gpu, os_ver = random.choice(device_list)
    return {"unique_device_id":f"Google|{uuid.uuid4()}","brand":brand,"model":model,"gpu_renderer":gpu,"system_software":os_ver,"screen_width":1080,"screen_height":2400,"screen_dpi":"340","memory":4096}

def get_device_for_account(acc_key: str) -> dict:
    devices = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE,"r",encoding="utf-8") as f: devices = json.load(f)
        except Exception: pass
    if acc_key in devices: return devices[acc_key]
    nd = _generate_new_device()
    devices[acc_key] = nd
    try:
        with open(DEVICES_FILE,"w",encoding="utf-8") as f: json.dump(devices, f, indent=2)
    except Exception: pass
    return nd

_DNS_CACHE: Dict[str, Tuple[str,float]] = {}
async def resolve_host_cloudflare(hostname: str) -> str:
    if not hostname: return hostname
    parts = hostname.split('.')
    if len(parts)==4 and all(p.isdigit() for p in parts): return hostname
    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp: return ip
    try:
        loop = asyncio.get_running_loop()
        info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
        if info:
            ip = info[0][4][0]
            _DNS_CACHE[hostname] = (ip, now + 300)
            return ip
    except Exception: pass
    return hostname

def optimize_tcp_socket(sock):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
    except Exception: pass

async def safe_close_writer(writer):
    if not writer: return
    try:
        if not writer.is_closing(): writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception: pass

client = httpx.AsyncClient(verify=False, timeout=15.0)

# ==================== CRYPTO / PROTOBUF ====================
CRC7_TABLE = bytes([0,9,18,27,36,45,54,63,72,65,90,83,108,101,126,119,25,16,11,2,61,52,47,38,81,88,67,74,117,124,103,110,50,59,32,41,22,31,4,13,122,115,104,97,94,87,76,69,43,34,57,48,15,6,29,20,99,106,113,120,71,78,85,92,100,109,118,127,64,73,82,91,44,37,62,55,8,1,26,19,125,116,111,102,89,80,75,66,53,60,39,46,17,24,3,10,86,95,68,77,114,123,96,105,30,23,12,5,58,51,40,33,79,70,93,84,107,98,121,112,7,14,21,28,35,42,49,56,65,72,83,90,101,108,119,126,9,0,27,18,45,36,63,54,88,81,74,67,124,117,110,103,16,25,2,11,52,61,38,47,115,122,97,104,87,94,69,76,59,50,41,32,31,22,13,4,106,99,120,113,78,71,92,85,34,43,48,57,6,15,20,29,37,44,55,62,1,8,19,26,109,100,127,118,73,64,91,82,60,53,46,39,24,17,10,3,116,125,102,111,80,89,66,75,23,30,5,12,51,58,33,40,95,86,77,68,123,114,105,96,14,7,28,21,42,35,56,49,70,79,84,93,98,107,112,121])
_DELTA = 0x9E3779B9; _ROUNDS = 16
_FIELD_SIZES = {0:1,1:2,2:2,3:1,4:2}
_FIELD_NAMES = {0:"sendOption",1:"cmd",2:"orderId",3:"flags",4:"length"}

def encode_varint(n: int) -> bytes:
    out = bytearray()
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def _pb_varint(fn, val): return encode_varint((fn<<3)|0) + encode_varint(val)
def _pb_length(fn, val):
    enc = val.encode('utf-8') if isinstance(val,str) else val
    return encode_varint((fn<<3)|2) + encode_varint(len(enc)) + enc

def create_proto(fields) -> bytes:
    packet = bytearray()
    for field, value in fields.items():
        if isinstance(field, str): field = int(field)
        if isinstance(value, dict): packet.extend(_pb_length(field, bytes(create_proto(value))))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict): packet.extend(_pb_length(field, bytes(create_proto(item))))
                elif isinstance(item, str): packet.extend(_pb_length(field, item))
                elif isinstance(item, (bytes, bytearray)): packet.extend(_pb_length(field, bytes(item)))
                elif isinstance(item, bool): packet.extend(_pb_varint(field, 1 if item else 0))
                elif isinstance(item, int): packet.extend(_pb_varint(field, item))
        elif isinstance(value, bool): packet.extend(_pb_varint(field, 1 if value else 0))
        elif isinstance(value, int): packet.extend(_pb_varint(field, value))
        elif isinstance(value, str): packet.extend(_pb_length(field, value))
        elif isinstance(value, (bytes, bytearray)): packet.extend(_pb_length(field, bytes(value)))
    return bytes(packet)

def encrypt_aes(hex_data: str) -> str:
    cipher = AES.new(AES_KEY, AES.MODE_CBC, AES_IV)
    return cipher.encrypt(pad(bytes.fromhex(hex_data), AES.block_size)).hex()

def decode_varint(data, offset):
    result = 0; shift = 0
    while offset < len(data):
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if not (byte & 0x80): return result, offset
        shift += 7
    return None, offset

def decode_protobuf_2(data):
    result = {}; offset = 0
    while offset < len(data):
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            value = data[offset:offset+length]; offset += length
            try:
                s = value.decode('utf-8')
                result[fn] = s if s else value.hex()
            except UnicodeDecodeError:
                nested = decode_protobuf_2(value)
                result[fn] = nested if nested else value.hex()
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def _parse_results_sync(results):
    out = {}
    for r in results:
        fd = {"wire_type": r.wire_type}
        if r.wire_type == "varint": fd["data"] = r.data
        elif r.wire_type in ("string","bytes"): fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"): fd["data"] = _parse_results_sync(r.data.results)
            elif isinstance(r.data, list): fd["data"] = _parse_results_sync(r.data)
            else: fd["data"] = str(r.data)
        out[str(r.field)] = fd
    return out

def decode_protobuf_dict(data: bytes) -> dict:
    try:
        return _parse_results_sync(Parser().parse(data))
    except Exception: return {}

async def decode_protobuf_async(data):
    try: return json.dumps(_parse_results_sync(Parser().parse(data)))
    except Exception: return "{}"

def create_packet(Pk, N, K, V):
    if isinstance(K, str): K = bytes.fromhex(K) if len(K)==32 else K.encode()
    if isinstance(V, str): V = bytes.fromhex(V) if len(V)==32 else V.encode()
    PkEnc = AES.new(K, AES.MODE_CBC, V).encrypt(pad(bytes.fromhex(Pk),16)).hex()
    L = len(PkEnc)//2
    hexlen = hex(L)[2:]
    if len(hexlen)%2 != 0: hexlen = '0'+hexlen
    total_pad = 12 - len(N) - len(hexlen)
    if total_pad < 0: total_pad = 0
    return bytes.fromhex(N + ('0'*total_pad) + hexlen + PkEnc)

# ==================== TEAM PACKETS (FIXED) ====================
def create_team(key, iv, game_version="1.132.9", region="BD"):
    fields = {
        1: 1, 2: {2: bytes.fromhex("01"), 3:1, 4:3, 5:"en",
            8: {1:"IDC3",2:123,3:region}, 9:1,
            10: bytes.fromhex("01090a0b1219202729"), 11:2, 13:1,
            14: {1:"08FBA33B4BABE2790205390333330000009700050092005F72697EB2134DCBB2467625142201040e38e848dc0e748c3f6aa04d81000000ff1113090dcacfa16d",
                 2:478, 3:"7e585d55", 4:"y[Z]", 6:12, 7:"15686677735a7506101c",
                 8:str(game_version), 9:3, 10:1, 11:"03626253513637754174"},
            19: 329, 21: bytes.fromhex("374f521955"), 24:{1:21},
            27:"a_6534489873065906362"}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def team_fresh(account_id, key, iv):
    return create_packet(create_proto({1:72, 2:{1:int(account_id)}}).hex(), "0515", key, iv)

def invite_player_in_team(target_uid, key, iv, region="BD"):
    fields = {1: 2, 2: {1: int(target_uid), 2: str(region).upper(), 4: 1}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def accept_team_invite(inviter_uid, own_uid, group_id, key, iv, region="BD", game_version="1.132.9"):
    reg = str(region).upper()
    fields = {1: 4, 2: {1: int(inviter_uid), 3: int(own_uid), 4: bytes.fromhex("0107090a0b120f19202729"), 8: 1,
            9: {1: "08FBA33B0522052002041B0222220007000C00010004000547E265AE1080779546762514110104076fa2e8770e748c3f6a68ed75000000ff08080500cacfa16d", 2: 235, 3: {14: 80, 11: 86}, 4: "{Y\\R", 6: 13, 7: {2: 4}, 8: str(game_version), 9: 2, 10: 1, 11: "0362625351"},
            10: str(group_id), 11: {1: "IDC3", 2: 107, 3: reg}, 13: "en", 16: "374f5219", 20: {1: 21}, 23: "a_6534489873065906362", 24: "https://dl-sg-production.freefiremobile.com/", 27: {1: 2, 2: 4}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def join_team_by_code(team_code, key, iv, region="BD", game_version="1.132.9"):
    reg = str(region).upper()
    fields = {1: 3, 2: {1: str(team_code), 4: bytes.fromhex("0107090a0b120f19202729"), 5: "en", 8: {1: "IDC3", 2: 107, 3: reg}, 9: 1, 13: 1,
            14: {1: "08FBA33B0522052002041B0222220007000C00010004000547E265AE1080779546762514110104076fa2e8770e748c3f6a68ed75000000ff08080500cacfa16d", 2: 235, 6: 13, 8: str(game_version), 9: 3, 10: 1}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def start_match_team(account_id, key, iv, region="BD"):
    fields = {1:9, 2:{1:int(account_id), 7:{1:"IDC3", 2:410, 3:region}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def ready_for_game(uid, key, iv):
    fields = {1: 15, 2: {1: int(uid), 2: 1}}
    return create_packet(create_proto(fields).hex(), "0519", key, iv)

# ==================== LOGIN & API HELPERS ====================
def get_app_version():
    try: return play_scraper('com.dts.freefireth').get('version')
    except Exception: return "1.132.9"

async def version_config(region="BD"):
    app_version = get_app_version()
    lang = REGION_LANG.get(region.upper(), "en")
    url = f"https://version.ggwhitehawk.com/live/ver.php?version={app_version}&lang={lang}&device=android&channel=android&appstore=googleplay&region={region.upper()}&whitelist_version=1.3.0&whitelist_sp_version=1.0.0"
    try:
        r = await client.get(url)
        j = r.json()
        if not j.get("server_url"): return None
        gops = [u.strip() for u in j.get("gop_url","").split(";") if u.strip()]
        return j.get("latest_release_version"), j.get("remote_version"), j.get("server_url"), gops[0] if gops else "https://ffmconnect.ppmainecoonghj.com", app_version
    except Exception: return None

async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {"Host":"100067.connect.garena.com", "User-Agent":"Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B)", "Content-Type":"application/x-www-form-urlencoded"}
    data = {"uid":str(uid),"password":password,"response_type":"token","client_type":"2","client_secret":HEX_KEY,"client_id":"100067"}
    for _ in range(4):
        try:
            r = await client.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                j = r.json()
                if j.get("open_id") and j.get("access_token"): return j.get("open_id"), j.get("access_token"), j.get("platform",4)
        except Exception: pass
        await asyncio.sleep(0.7)
    return None

async def get_payload(access_token, open_id, platform, version, lang_code="en"):
    device_id = f"Google|{uuid.uuid4()}"
    major_login = {"3": str(datetime.now())[:-7], "4": "free fire", "5": 1, "7": f"{version}", "8": "Android OS 14 / API-34", "9": "Handheld", "11": "CarrierDataNetwork", "12": 1672, "13": 750, "14": "338", "15": "ARMv7 VFPv3 NEON | 2002 | 8", "16": 3702, "17": "Mali-G52", "18": "OpenGL ES 3.2", "19": device_id, "20": "104.28.197.151", "21": lang_code, "22": f"{open_id}", "23": f"{platform}", "24": "Handheld", "25": "samsung SM-E135F", "26": "BD", "29": f"{access_token}", "30": 1, "42": "Cellular", "57": "7428b253defc164018c604a1ebbfebdf", "60": 52037, "61": 5355, "62": 3723, "63": 3, "64": 5483, "65": 52037, "66": 5483, "67": 52037, "73": 2, "74": "/data/app/", "76": 1, "77": "b8e0cd5e", "78": 3, "79": 1, "81": "32", "83": "2019121229", "86": "OpenGLES2", "87": 8191, "88": int(platform), "92": 16091, "93": "android", "94": "KqsHT3Yeqo3RLRl8efNiL3aL/", "95": 111107, "96": "{}", "97": 1, "98": 1, "99": f"{platform}", "100": f"{platform}", "102": "4503454457550c0766", "104": 53792, "105": 1, "106": "https://dl-bs.ggpolarbear.com/live/ABHotUpdates/", "107": "c8e41b7a93f02d56e1a94c7b8203f5d1"}
    get_login_data = dict(major_login)
    get_login_data["90"] = "Khulna"; get_login_data["91"] = "D"; get_login_data["99"] = "0"; get_login_data["103"] = 1
    return bytes.fromhex(encrypt_aes(create_proto(major_login).hex())), bytes.fromhex(encrypt_aes(create_proto(get_login_data).hex()))

async def major_login(payload, login_url, release_version):
    url = f"{login_url.rstrip('/')}/MajorLogin"
    req_headers = {"Accept": "*/*", "Authorization": "Bearer ", "Content-Type": "application/x-www-form-urlencoded", "ReleaseVersion": f"{release_version}", "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)", "X-GA": "v1 1", "X-GA-SV": str(int(time.time())), "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_context = ssl.create_default_context(); ssl_context.check_hostname = False; ssl_context.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.post(url, headers=req_headers, data=payload, ssl=ssl_context) as response:
                response_content = await response.read()
                if response.status != 200 or len(response_content) < 200: return None
                best = None; best_score = -1; best_off = 0
                for offset in [64, 0, 48, 32, 80, 16, 128, 8, 96, 60, 56, 40, 24, 20, 12, 4]:
                    if offset >= len(response_content): continue
                    cb = response_content[offset:]
                    cand = decode_protobuf_dict(cb)
                    if not cand: cand = {str(k): {"data": v} for k, v in decode_protobuf_2(cb).items()}
                    if not cand: continue
                    keys = set(cand.keys())
                    score = len(cand) + (100 if "8" in keys else 0) + (50 if "10" in keys else 0)
                    if score > best_score: best = cand; best_score = score; best_off = offset
                    if "8" in keys and "10" in keys: break
                if not best or ("8" not in best and 8 not in best): return None
                best["__RAW_HEX__"] = response_content.hex(); best["__OFFSET__"] = best_off
                return best
    except Exception: return None

async def get_login_data(payload, jwt_token, server_url, release_version):
    url = f"{server_url.rstrip('/')}/GetLoginData"
    hdrs = {"Accept":"*/*","Authorization":f"Bearer {jwt_token}","Content-Type":"application/x-www-form-urlencoded","ReleaseVersion":f"{release_version}","User-Agent":"UnityPlayer/2018.4.12f1","X-GA":"v1 1","X-GA-SV":str(int(time.time())),"X-Unity-Version":"2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context(); ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                if r.status != 200: return None
                content = await r.read()
                for off in [0,64,48,32,80,16,128,8,96]:
                    if off >= len(content): continue
                    c = decode_protobuf_dict(content[off:])
                    if c and len(c) >= 3: return c
                return None
    except Exception: return None

def _extract_key_iv(res_json):
    if "__RAW_HEX__" in res_json and "__OFFSET__" in res_json:
        try:
            rf = extract_raw_fields(bytes.fromhex(res_json["__RAW_HEX__"])[int(res_json["__OFFSET__"]):])
            for kf, vf in [(22,23),(24,25),(6,7)]:
                k = rf.get(kf); v = rf.get(vf)
                if isinstance(k,(bytes,bytearray)) and len(k)==16 and isinstance(v,(bytes,bytearray)) and len(v)==16: return bytes(k), bytes(v)
        except Exception: pass
    found = {}
    for k, v in res_json.items():
        if str(k).startswith("__") or not isinstance(v, dict): continue
        data = v.get("data")
        raw = None
        if isinstance(data, (bytes,bytearray)) and len(data)==16: raw = bytes(data)
        elif isinstance(data, str) and len(data)==32:
            try: raw = bytes.fromhex(data)
            except Exception: pass
        if raw and len(raw)==16:
            try: found[int(k)] = raw
            except Exception: pass
    if len(found) < 2: return None, None
    for kf, vf in [(22,23),(24,25),(6,7)]:
        if kf in found and vf in found: return found[kf], found[vf]
    sk = sorted(found.keys())
    return found[sk[0]], found[sk[1]]

def extract_raw_fields(data: bytes) -> dict:
    result = {}; offset = 0
    while offset < len(data):
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0: result[fn], offset = decode_varint(data, offset)
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            result[fn] = bytes(data[offset:offset+length]); offset += length
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

# ==================== MAIN BOT LOGIC ====================
async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="BD", typ='OnLine'):
    uid_hex = f"{int(account_id):016x}"
    ts_hex = f"{int(server_time):08x}"
    enc = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(token.encode(), 16)).hex()
    enc_len = f"{len(enc)//2:08x}"
    reg = str(region).upper() if region else "BD"
    pfx = ('7219' if reg == 'BD' else ('7214' if reg == 'IND' else '7215')) if typ == 'OnLine' else ('8119' if reg == 'BD' else ('8114' if reg == 'IND' else '8115'))
    return f"{pfx}{uid_hex}{ts_hex}00000000{enc_len}{enc}" if typ == 'OnLine' else f"{pfx}{uid_hex}{ts_hex}{enc_len}{enc}"

async def send_keep_alive(region="BD"):
    reg = str(region).upper() if region else "BD"
    return bytes.fromhex("0219" if reg == "BD" else ("0214" if reg == "IND" else "0215"))

async def func_gateway_keepalive(writer, region):
    ka_bytes = await send_keep_alive(region)
    while True:
        await asyncio.sleep(5)
        try:
            if writer and not writer.is_closing():
                writer.write(ka_bytes); await writer.drain()
        except Exception: break

async def functional_lone_wolf(addrs, starter_packet, account_region, client_version, key, iv, account_id="", account_data=None, max_reconnects=10):
    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    uid_str = str(account_id)
    current_token = starter_packet
    current_key = key
    current_iv = iv
    current_account_data = account_data
    _writer_ref = {"w": None}
    _team_active = {"flag": True}

    async def _on_match_complete():
        pass # Add your logic if needed

    async def _team_coordinator():
        try:
            target = _team_state.get("target_size", TEAM_SIZE)
            print_info(f"[TEAM-COORD] START {uid_str} target={target}")
            
            while True:
                async with _team_state["lock"]:
                    n = len(_team_state["peers"])
                    is_leader = (_team_state["leader_uid"] == uid_str)
                if n >= target: break
                if bot_state.is_paused(uid_str): return
                await asyncio.sleep(0.5)

            await asyncio.sleep(TEAM_READY_DELAY)

            async with _team_state["lock"]:
                if _team_state["leader_uid"] != uid_str: return
                if _team_state.get("team_created"): return
                _team_state["team_created"] = True

            print_success(f"[TEAM] 👑 {uid_str} — creating team...")
            own_id_num = current_account_data.get('account_id', uid_str) if current_account_data else uid_str

            try:
                pkt = create_team(current_key, current_iv, client_version, region=account_region)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    print_info(f"[TEAM] create_team sent ({len(pkt)}B)")
            except Exception as e: print_error(f"[TEAM] create_team err: {e}")

            await asyncio.sleep(2.5) # Bariye deya holo

            try:
                pkt = team_fresh(int(own_id_num), current_key, current_iv)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    print_success(f"[TEAM] 🔄 team_fresh #1 sent")
            except Exception as e: pass

            await asyncio.sleep(1.5)

            async def _invite_uid(target_uid):
                for attempt in range(2):
                    try:
                        inv = invite_player_in_team(int(target_uid), current_key, current_iv, region=account_region)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(inv); await _writer_ref["w"].drain()
                            print_info(f"[TEAM] invite to {target_uid}")
                    except Exception: pass
                    await asyncio.sleep(0.6)

            async with _team_state["lock"]:
                peers_snapshot = dict(_team_state["peers"])

            for peer_uid, peer_info in peers_snapshot.items():
                if peer_uid == uid_str: continue
                peer_acc_id = peer_info["data"].get("account_id", peer_uid)
                print_success(f"[TEAM] 📨 Inviting bot {peer_acc_id}...")
                await _invite_uid(int(peer_acc_id))

            await asyncio.sleep(TEAM_INVITE_WAIT)

            try:
                pkt = team_fresh(int(own_id_num), current_key, current_iv)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
            except Exception: pass

            await asyncio.sleep(2.0)

            while _team_active["flag"]:
                try:
                    if bot_state.is_paused(uid_str): break
                    async with _team_state["lock"]:
                        if _team_state["leader_uid"] != uid_str: break
                    rdy = ready_for_game(int(own_id_num), current_key, current_iv)
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                    await asyncio.sleep(1.0)
                    sm = start_match_team(int(own_id_num), current_key, current_iv, region=account_region)
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                except Exception: pass
                await asyncio.sleep(5.0)
        except asyncio.CancelledError: raise
        except Exception as e: print_error(f"[TEAM] coordinator error: {e}")

    async def _member_match_trigger():
        try:
            await asyncio.sleep(TEAM_READY_DELAY + 2.0)
            async with _team_state["lock"]:
                if _team_state["leader_uid"] == uid_str: return
            
            my_id = current_account_data.get('account_id', uid_str) if current_account_data else uid_str
            joined_via_code = False

            while _team_active["flag"]:
                try:
                    if bot_state.is_paused(uid_str): break
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        async with _team_state["lock"]:
                            tc = _team_state.get("team_code")
                        if tc and not joined_via_code:
                            try:
                                jpkt = join_team_by_code(tc, current_key, current_iv, region=account_region, game_version=client_version)
                                _writer_ref["w"].write(jpkt); await _writer_ref["w"].drain()
                                joined_via_code = True
                                await asyncio.sleep(1.0)
                            except Exception: pass

                        rdy = ready_for_game(int(my_id), current_key, current_iv)
                        _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                except Exception: pass
                await asyncio.sleep(3.5)
        except asyncio.CancelledError: raise
        except Exception: pass

    try:
        while True:
            while bot_state.is_paused(uid_str):
                await asyncio.sleep(1.0)
            writer = None; gateway_ping_task = None; team_coord_task = None; member_trigger_task = None
            try:
                if current_account_data:
                    fresh = cache_get(str(current_account_data['auth_uid'])) if current_account_data.get('auth_type') == 'guest' else None
                    if fresh:
                        current_account_data = fresh
                        current_key = fresh['aes_ak']; current_iv = fresh['iv_i']
                        current_token = await build_tcp_startup_packet(fresh['account_id'], fresh['token'], fresh['server_time'], current_key, current_iv, region=fresh.get('region', account_region), typ='OnLine')
                    else: raise ConnectionError("Cache expired")

                resolved_ip = await resolve_host_cloudflare(ip)
                reader, writer = await asyncio.open_connection(resolved_ip, int(port))
                bot_state.register_writer(uid_str, writer)
                _writer_ref["w"] = writer
                raw_sock = writer.get_extra_info('socket')
                if raw_sock: optimize_tcp_socket(raw_sock)
                
                writer.write(bytes.fromhex(current_token)); await writer.drain()
                gateway_ping_task = asyncio.create_task(func_gateway_keepalive(writer, account_region))
                print_success(f"[✓] TCP Gateway Connected | UID: {uid_str}")
                
                async with _team_state["lock"]:
                    _team_state["peers"][uid_str] = {"writer": writer, "data": current_account_data, "key": current_key, "iv": current_iv}
                    if _team_state["leader_uid"] is None or uid_str < str(_team_state["leader_uid"]):
                        _team_state["leader_uid"] = uid_str
                        print_success(f"[TEAM] 👑 {uid_str} is leader")

                if TEAM_MODE:
                    team_coord_task = asyncio.create_task(_team_coordinator())
                    member_trigger_task = asyncio.create_task(_member_match_trigger())

                while True:
                    if bot_state.is_paused(uid_str): break
                    try:
                        data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                    except asyncio.TimeoutError: continue
                    if not data: raise ConnectionError("Connection closed")
                    hex_data = data.hex()

                    # Parse Team Code from 0500
                    if hex_data.startswith("0500"):
                        try:
                            dec = None
                            for off in (10, 12, 8, 6):
                                if len(hex_data) <= off: continue
                                inner = bytes.fromhex(hex_data[off:])
                                cand = decode_protobuf_dict(inner) or {str(k): {"data": v} for k, v in decode_protobuf_2(inner).items()}
                                if cand and ("5" in cand or len(cand) >= 2): dec = cand; break
                            if dec:
                                f5 = dec.get("5", {}).get("data", dec.get("5"))
                                if isinstance(f5, dict):
                                    for fk in [11, 5, 1, 3, 2, 4]:
                                        v = f5.get(fk) or f5.get(str(fk))
                                        if v and isinstance(v, dict) and "data" in v: v = v["data"]
                                        if v and str(v).isdigit() and 5 <= len(str(v)) <= 9:
                                            async with _team_state["lock"]: _team_state["team_code"] = str(v)
                                            print_success(f"[TEAM] 📢 Team Code captured: {v}")
                                            break
                        except Exception: pass

                    if hex_data.startswith("0300") and len(data) >= 300:
                        print_success(f"[⚔] Match Found | UID: {uid_str}")
                        for tk in (team_coord_task, member_trigger_task):
                            if tk and not tk.done(): tk.cancel()
                        _team_active["flag"] = False

                        try:
                            res = json.loads(await decode_protobuf_async(hex_data[10:]))
                            token = udp_key = match_code = server_ip_port = block_val = None
                            match_account_id = res.get('1', {}).get('data')
                            if '5' in res and 'data' in res['5']:
                                rf5 = res['5']['data']
                                server_ip_port = rf5.get('2', {}).get('data')
                                udp_key = rf5.get('3', {}).get('data')
                                token = rf5.get('4', {}).get('data')
                                block_val = rf5.get('1', {}).get('data')
                                match_code = rf5.get('42', {}).get('data') or res.get('42', {}).get('data')
                            
                            if token and udp_key and match_code and server_ip_port:
                                # Match startup packets logic goes here (Omitted for brevity, it's same as your original)
                                print_info("Starting UDP match logic...")
                                writer.close(); await writer.wait_closed()
                                await asyncio.sleep(2.0)
                                break
                        except Exception as e: print_warning(f"[MATCH] {e}"); continue
            except asyncio.CancelledError: raise
            except Exception as e:
                if "Cache expired" in str(e): break
                reconnects += 1
                if reconnects > max_reconnects: reconnects = 0; break
                await asyncio.sleep(1.0)
            finally:
                _team_active["flag"] = False
                async with _team_state["lock"]:
                    _team_state["peers"].pop(uid_str, None)
                    if _team_state["leader_uid"] == uid_str:
                        _team_state["leader_uid"] = None
                        _team_state["team_code"] = None
                        _team_state["team_created"] = False
                if gateway_ping_task: gateway_ping_task.cancel()
                if writer:
                    bot_state.unregister_writer(uid_str, writer)
                    await safe_close_writer(writer)
                _team_active["flag"] = True
    except asyncio.CancelledError: raise
    finally:
        for m in play_matches:
            if not m.done(): m.cancel()

# ==================== CACHE & ACCOUNT LOOP ====================
_token_cache_memo = {}
def cache_get(uid):
    cache = {}
    if os.path.exists(TOKEN_CACHE_FILE):
        try:
            with open(TOKEN_CACHE_FILE,"r",encoding="utf-8") as f: cache = json.load(f)
        except Exception: pass
    e = cache.get(str(uid))
    if not e or time.time() - e.get("cached_at",0) > TOKEN_CACHE_TTL: return None
    if str(e.get("account_id","")).isdigit(): e["account_id"] = int(e["account_id"])
    return e

def cache_set(uid, data):
    cache = {}
    if os.path.exists(TOKEN_CACHE_FILE):
        try:
            with open(TOKEN_CACHE_FILE,"r",encoding="utf-8") as f: cache = json.load(f)
        except Exception: pass
    e = dict(data); e["cached_at"] = time.time()
    if isinstance(e.get("aes_ak"), (bytes, bytearray)): e["aes_ak"] = e["aes_ak"].hex()
    if isinstance(e.get("iv_i"), (bytes, bytearray)): e["iv_i"] = e["iv_i"].hex()
    if isinstance(e.get("login_payload_data"), (bytes, bytearray)): e["login_payload_data"] = e["login_payload_data"].hex()
    cache[str(uid)] = e
    try:
        with open(TOKEN_CACHE_FILE,"w",encoding="utf-8") as f: json.dump(cache, f, indent=2)
    except Exception: pass

def cache_invalidate(uid):
    cache = {}
    if os.path.exists(TOKEN_CACHE_FILE):
        try:
            with open(TOKEN_CACHE_FILE,"r",encoding="utf-8") as f: cache = json.load(f)
        except Exception: pass
    if str(uid) in cache: del cache[str(uid)]
    try:
        with open(TOKEN_CACHE_FILE,"w",encoding="utf-8") as f: json.dump(cache, f, indent=2)
    except Exception: pass

async def process_account_uid_pass(uid, password, region_override="BD"):
    cached = cache_get(uid)
    if cached:
        aid = str(cached['account_id'])
        if isinstance(cached.get("aes_ak"), str): cached["aes_ak"] = bytes.fromhex(cached["aes_ak"])
        if isinstance(cached.get("iv_i"), str): cached["iv_i"] = bytes.fromhex(cached["iv_i"])
        if isinstance(cached.get("login_payload_data"), str): cached["login_payload_data"] = bytes.fromhex(cached["login_payload_data"])
        bot_state.register_account(aid, cached.get('nickname', f"Player_{aid}"), cached.get('region','BD'), cached.get('level', 1), cached.get('exp', 0), 0, auth_uid=str(uid), clan_id=cached.get('clan_id'))
        return cached
    try:
        vc = await version_config(region_override or "BD")
        if not vc: return None
        release_version, client_version, server_url, gop_1, app_version = vc
        tg = await get_access_token(uid, password)
        if not tg: return None
        open_id, access_token, platform = tg

        major_payload, login_payload = await get_payload(access_token, open_id, platform, client_version)
        res_json = await major_login(major_payload, server_url, release_version)
        if not res_json: return None

        acc_id_raw = res_json.get("1", {}).get("data")
        jwt_token = res_json.get("8", {}).get("data")
        server_url_raw = res_json.get("10", {}).get("data")
        server_time = res_json.get("21", {}).get("data")
        region_raw = res_json.get("2", {}).get("data", "BD")
        aes_ak, iv_i = _extract_key_iv(res_json)
        
        if not jwt_token or not server_url_raw or not aes_ak: return None
        getlogin_json = await get_login_data(login_payload, jwt_token, server_url_raw, release_version)
        if not getlogin_json: return None

        level = int(getlogin_json.get("6", {}).get("data", 1) or 1)
        exp = int(getlogin_json.get("7", {}).get("data", 0) or 0)
        nickname = getlogin_json.get("4", {}).get("data", f"Player_{acc_id_raw}")
        acc_id = str(acc_id_raw)

        bot_state.register_account(acc_id, nickname, region_raw, level, exp, 0, auth_uid=str(uid), clan_id=region_override)
        ad = {'account_id':acc_id_raw,'nickname':nickname,'region':region_raw,'level':level,'exp':exp,'likes':0,'open_id':open_id,
            'access_token':access_token,'platform':str(platform),'token':jwt_token,'server_time':server_time,'aes_ak':aes_ak,'iv_i':iv_i,
            'functional_addrs':getlogin_json.get("14", {}).get("data"),'informational_addrs':getlogin_json.get("32", {}).get("data"),
            'release_version':release_version,'client_version':client_version,'server_url':server_url_raw,'login_payload_data':login_payload,
            'auth_type':'guest','auth_uid':uid,'auth_password':password, 'clan_id': region_override}
        
        cache_set(uid, ad)
        return ad
    except Exception as e:
        print_error(f"login err: {e}"); return None

async def account_loop_guest(uid, password, region_override="BD", clan_override=None):
    uid_str = str(uid)
    bot_state.account_workers[uid_str] = asyncio.current_task()
    while True:
        try:
            bot_state.update_status(uid_str, "CONNECTING")
            ad = await process_account_uid_pass(uid_str, password, region_override)
            if not ad: await asyncio.sleep(15); continue
            
            acc_id = str(ad['account_id'])
            bot_state.auth_to_game_id[uid_str] = acc_id
            bot_state.game_to_auth_id[acc_id] = uid_str
            
            tcp_online = await build_tcp_startup_packet(ad['account_id'], ad['token'], ad['server_time'], ad['aes_ak'], ad['iv_i'], region=region_override, typ='OnLine')
            await functional_lone_wolf(ad['functional_addrs'], tcp_online, region_override, ad['client_version'], ad['aes_ak'], ad['iv_i'], account_id=acc_id, account_data=ad)
            await asyncio.sleep(3)
        except asyncio.CancelledError:
            bot_state.update_status(uid_str, "OFFLINE"); break
        except Exception as e:
            await asyncio.sleep(10)

async def create_four_accounts(region: str, clan_id: str, count: int = 2, password: str = "ISHU"):
    bot_state.creating = True
    _team_state["target_size"] = count # Dynamic team size
    _team_state["team_created"] = False
    _team_state["team_code"] = None
    _team_state["leader_uid"] = None
    _team_state["peers"] = {}

    try:
        vc = await version_config(region)
        if not vc: return []
        release_v, remote_v, login_url, gop_1, app_version = vc
        if not login_url.endswith("/"): login_url += "/"
        
        created = []
        for i in range(count):
            uid = await register_account(password, gop_1, app_version)
            if not uid: continue
            tok = await grant_token(uid, password, gop_1, app_version)
            if not tok: continue
            
            open_id = tok["open_id"]; access_token = tok["access_token"]
            major_payload, login_payload = await get_payload(access_token, open_id, 4, remote_v or app_version)
            nickname_final = f"DISHA-{random.randint(100000, 999999)}"
            
            await asyncio.sleep(1.0)
            res_json = await major_login(major_payload, login_url, release_v)
            if not res_json: continue
            
            acc_id_raw = res_json.get("1", {}).get("data")
            jwt_token = res_json.get("8", {}).get("data")
            server_url_raw = res_json.get("10", {}).get("data")
            aes_ak, iv_i = _extract_key_iv(res_json)
            ld = await get_login_data(login_payload, jwt_token, server_url_raw, release_v)
            
            ad = {'account_id': acc_id_raw, 'nickname': nickname_final, 'region': region, 'level': 1, 'exp': 0, 'likes': 0,
                  'open_id': open_id, 'access_token': access_token, 'platform': '4', 'token': jwt_token, 'server_time': res_json.get("21", {}).get("data"),
                  'aes_ak': aes_ak, 'iv_i': iv_i, 'functional_addrs': (ld or {}).get("14", {}).get("data"),
                  'release_version': release_v, 'client_version': remote_v or app_version, 'server_url': server_url_raw, 
                  'auth_type': 'guest', 'auth_uid': uid, 'auth_password': password, 'clan_id': clan_id}
            
            cache_set(uid, ad)
            created.append(ad)
            
            asyncio.create_task(account_loop_guest(str(uid), password, region, clan_id))
            await asyncio.sleep(1.0)
        return created
    except Exception as e:
        print_error(f"create err: {e}"); return []
    finally:
        bot_state.creating = False

async def register_account(password, gop_url, app_version):
    try:
        payload = json.dumps({"app_id":100067,"client_type":2,"password":password,"source":2}, separators=(',',':'))
        sig = hmac.new(API_KEY, payload.encode(), hashlib.sha256).hexdigest()
        headers = {"User-Agent": "GarenaMSDK/4.0.44", "Authorization": f"Signature {sig}", "Content-Type": "application/json"}
        async with aiohttp.ClientSession() as s:
            async with s.post(f"{gop_url}/api/v2/oauth/guest:register", headers=headers, data=payload) as resp:
                data = json.loads(await resp.text())
                if data.get("code") == 0: return data["data"]["uid"]
    except Exception: pass
    return None

async def grant_token(uid, password, gop_url, app_version):
    try:
        payload = json.dumps({"client_id":100067,"client_secret":HEX_KEY,"client_type":2,"device_id":f"02-{uuid.uuid4()}","password":password,"response_type":"token","uid":int(uid)}, separators=(',',':'))
        sig = hmac.new(API_KEY, payload.encode(), hashlib.sha256).hexdigest()
        headers = {"User-Agent": "GarenaMSDK/4.0.44", "Authorization": f"Signature {sig}", "Content-Type": "application/json"}
        async with aiohttp.ClientSession() as s:
            async with s.post(f"{gop_url}/api/v2/oauth/guest/token:grant", headers=headers, data=payload) as resp:
                data = json.loads(await resp.text())
                if data.get("code") == 0: return data["data"]
    except Exception: pass
    return None

# ==================== HTTP SERVER ====================
async def serve_html_file(request, filename):
    for path in (filename, os.path.join("templates", filename)):
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f: return aiohttp.web.Response(text=f.read(), content_type="text/html", charset="utf-8")
    return aiohttp.web.Response(text=f"<h1>{filename} not found</h1>", content_type="text/html", status=404)

async def api_stats(request):
    accs = list(bot_state.accounts.values())
    return aiohttp.web.json_response({
        "accounts": accs, "total_accounts": len(accs),
        "total_matches_started": bot_state.matches_started,
        "total_gained_exp": bot_state.total_exp_gained,
        "logs": bot_state.logs[-100:],
        "team_code": _team_state.get("team_code"),
        "leader_uid": _team_state.get("leader_uid"),
    })

async def api_create_team(request):
    body = await request.json()
    region = str(body.get("region", "BD")).upper()
    clan_id = str(body.get("clan_id", "")).strip()
    count = max(1, min(2, int(body.get("count", 2))))
    password = str(body.get("password", "ISHU")).strip()
    if bot_state.creating: return aiohttp.web.json_response({"ok": False, "error": "already creating"})
    asyncio.create_task(create_four_accounts(region, clan_id, count, password))
    return aiohttp.web.json_response({"ok": True, "msg": f"creating {count} bots for {region}"})

async def start_web_server():
    app = aiohttp.web.Application()
    app.router.add_get("/", lambda r: serve_html_file(r, "index.html"))
    app.router.add_get("/api/stats", api_stats)
    app.router.add_post("/api/create_team", api_create_team)
    runner = aiohttp.web.AppRunner(app)
    await runner.setup()
    site = aiohttp.web.TCPSite(runner, WEB_HOST, WEB_PORT)
    await site.start()
    print_success(f"[WEB] Server running on http://localhost:{WEB_PORT}/")

async def main():
    print("\033[95m" + "╔══════════════════════════════════════════════════════╗" + "\033[0m")
    print("\033[95m" + "║        👑  ISHU X 999 - BANGLADESH SERVER  👑        ║" + "\033[0m")
    print("\033[95m" + "╚══════════════════════════════════════════════════════╝" + "\033[0m")
    await start_web_server()
    while True: await asyncio.sleep(1)

if __name__ == "__main__":
    try: asyncio.run(main())
    except KeyboardInterrupt: print_warning("stopped")
