#!/usr/bin/python

import sys
import codecs
import os
import base64
import marshal
import re
try:
    from hashlib import md5
except ImportError:
    import md5 as md5old
    md5 = lambda x='': md5old.md5(x)
import inspect
import time
import socket
import tempfile
import zlib
import zipfile
import re
import threading
from multiprocessing import Queue

global socket
import socket
class buderus_connect():
    def __init__(self):
        from multiprocessing import Queue
        import threading
        import re
        #self.id = "buderus_connect"
        #self.logik = localvars["pItem"]
        #self.MC = self.logik.MC
        #EN = localvars['EN']
        #self.device_connector = EN[1]
        ## Config
        self.config = {
            'debug': 0,                 # debug level (> 5) macht debug prints
            'readonly' : 1,             # wenn readyonly=1 , werden schreibende Befehle nicht zugelassen
            'writetime' : 0,            # wenn writetime=1 , wird das schreiben der Zeit zugelassen
            'delaydirectendtime' : 1.0, # wartezeit beim beenden des directmodes
        }
        # 3964R Constants
        self._constants = {
            'STX': chr(0x02),
            'DLE': chr(0x10),
            'ETX': chr(0x03),
            'NAK': chr(0x15),
            'QVZ': 2,             # Quittungsverzugzeit (QVZ) 2 sec
            'ZVZ': 0.220,         # Der Abstand zwischen zwei Zeichen darf nicht mehr als die Zeichenverzugszeit (ZVZ) von 220 ms
            'BWZ': 4,             # Blockwartezeit von 4 sec
        }
        ## Geraetetypen
        self.data_types = {
            "07" : ("Heizkreis 1", 18),
            "08" : ("Heizkreis 2", 18),
            "09" : ("Heizkreis 3", 18),
            "0A" : ("Heizkreis 4", 18),
            "0B" : ("Aussenparameter", 12),
            "0C" : ("Warmwasser", 12),
            "0D" : ("Konfiguration (Modulauswahl)", 18),
            "0E" : ("Strategie wandhaengend(UBA)", 18),
            "10" : ("Kessel bodenstehend", 18),
            "11" : ("Schaltuhr pro Woche Kanal 1", 18),
            "12" : ("Schaltuhr pro Woche Kanal 2", 18),
            "13" : ("Schaltuhr pro Woche Kanal 3", 18),
            "14" : ("Schaltuhr pro Woche Kanal 4", 18),
            "15" : ("Schaltuhr pro Woche Kanal 5", 18),
            "16" : ("Heizkreis 5", 18),
            "17" : ("Schaltuhr pro Woche Kanal 6", 18),
            "18" : ("Heizkreis 6", 18),
            "19" : ("Schaltuhr pro Woche Kanal 7", 18),
            "1A" : ("Heizkreis 7", 18),
            "1B" : ("Schaltuhr pro Woche Kanal 8", 18),
            "1C" : ("Heizkreis 8", 18),
            "1D" : ("Schaltuhr pro Woche Kanal 9", 18),
            "1F" : ("Schaltuhr pro Woche Kanal 10", 18),
            "20" : ("Strategie bodenstehend", 12),
            "24" : ("Solar", 12),
            "26" : ("Strategie (FM458)", 12),
            "80" : ("Heizkreis 1", 18),
            "81" : ("Heizkreis 2", 18),
            "82" : ("Heizkreis 3", 18),
            "83" : ("Heizkreis 4", 18),
            "84" : ("Warmwasser", 12),
            "85" : ("Strategie wandhaengend", 12),
            "87" : ("Fehlerprotokoll", 42),
            "88" : ("Kessel bodenstehend", 42),
            "89" : ("Konfiguration", 24),
            "8A" : ("Heizkreis 5", 18),
            "8B" : ("Heizkreis 6", 18),
            "8C" : ("Heizkreis 7", 18),
            "8D" : ("Heizkreis 8", 18),
            "8E" : ("Heizkreis 9", 18),
            "8F" : ("Strategie bodenstehend", 30),
            "90" : ("LAP", 18),
            "92" : ("Kessel 1 wandhaengend", 60),
            "93" : ("Kessel 2 wandhaengend", 60),
            "94" : ("Kessel 3 wandhaengend", 60),
            "95" : ("Kessel 4 wandhaengend", 60),
            "96" : ("Kessel 5 wandhaengend", 60),
            "97" : ("Kessel 6 wandhaengend", 60),
            "98" : ("Kessel 7 wandhaengend", 60),
            "99" : ("Kessel 8 wandhaengend", 60),
            "9A" : ("KNX FM446",60),
            "9B" : ("Waermemenge", 36),
            "9C" : ("Stoermeldemodul", 6),
            "9D" : ("Unterstation", 6),
            "9E" : ("Solarfunktion", 54),
            "9F" : ("alternativer Waermeerzeuger", 42),
        }
        ## List fuer gefundene Geraete
        self.found_devices = []
        ## List die Geraete IDs enthaellt bei denen Antworten ausstehen
        self.waiting_direct_bus = []
        ## threading Lock um _is_directmode und waiting_direct_bus zu beschreiben
        self.directmode_lock = threading.RLock()
        ## Derzeitiger Direct-mode status
        self._is_directmode = False
        self._moxa_thread = None
        ## Socket zum MOXA
        self.sock = None
        ## threading Lock fuer exklusives schreiben von entweder der Empfangs- oder Sende- Funktion
        self._buderus_data_lock = threading.RLock()

        ## Queue fuer Nachrichten zum Logamtik
        self._buderus_message_queue = Queue()

        ## Konfig an Eingang 2 parsen
        self.readconfig('A200')
        ## Mit dem Kommando "0xA2 <ECOCAN-BUS-Adresse>" koennen die Monitordaten des ausgewaehlten
        ## ECOCAN-BUS-Geraetes von der Kommunikationskarte ausgelesen werden.
        ## Mit Hilfe des Kommandos "0xB0 <ECOCAN-BUS-Adresse>" gefolgt von einem entsprechenden
        ## Datenblock koennen im Direkt-Modus einstellbare Parameter die fuer ein Regelgeraet bestimmt sind an die
        ## Schnittstelle geschickt werden. Die Schnittstelle schickt diese Daten dann weiter an das entsprechende
        ## Regelgeraet.
        self.directmode_regex = re.compile("(?P<id>A0|A1|A2|B3|B4)(?P<busnr>[0-9a-fA-F]{2})")
        self.directmode_regexes = {
            "A3" : re.compile("(?P<id>A3)(?P<busnr>[0-9a-fA-F]{2})(?P<Data_type>[0-9a-fA-F]{2})(?P<offset>[0-9a-fA-F]{2})"),
            "B0" : re.compile("(?P<id>B0)(?P<busnr>[0-9a-fA-F]{2})(?P<Data_type>[0-9a-fA-F]{2})(?P<offset>[0-9a-fA-F]{2})[0-9a-fA-F]{12}"),
            "B1" : re.compile("(?P<id>B1)"), ## Datum/Uhrzeit vom ECOBUS anfordern
            "B2" : re.compile("(?P<id>B2)[0-9a-fA-F]{12}"), ## Datum/Uhrzeit auf ECOBUS schreiben
        }
        ## Im "Normal-Modus" werden die Monitordaten nach folgendem Muster uebertragen:
        ## 0xA7 <ECOCAN-BUS-Adresse> <TYP> <OFFSET> <DATUM>
        ## 0xA7 = Kennung fuer einzelne Monitordaten
        ## ECOCAN-BUS-Adresse = Herkunft s Adresse des Monitordatum s (hier Regelgeraeteadresse)
        ## TYP = Typ der empfangenen Monitordaten
        ## OFFSET = Offset zur Einsortierung der Daten eines Typ s
        ## DATUM = eigentlicher Messwert
        ## Im "Direct-Modus" werden alle Monitordaten nach folgendem Muster uebertragen:
        ## 0xAB <ECOCAN-BUS-Adresse> <TYP> <OFFSET> <6 Daten-Byte>
        ## 0xAB = Kennung fuer Monitordaten
        ## ECOCAN-BUS-Adresse = die abgefragte Adresse zur Bestaetigung
        ## TYP = Typ der gesendeten Monitordaten
        ## Daten unter dem entsprechenden Typ werden nur gesendet wenn auch die entsprechende Funktionalitaet
        ## im Regelgeraet eingebaut ist.
        ## OFFSET = Offset zur Einsortierung der Daten eines Typ s
        ## Im "Direct-Modus" werden alle Einstellbaren Parameter nach folgendem Muster uebertragen:
        ## 0xA9 <ECOCAN-BUS-Adresse> <TYP> <OFFSET> <6 Daten-Byte>
        ## 0xA9 = Kennung fuer Monitordaten
        ## ECOCAN-BUS-Adresse = die abgefragte Adresse zur Bestaetigung
        ## TYP = Typ der gesendeten Monitordaten
        ## Daten unter dem entsprechenden Typ werden nur gesendet wenn auch die entsprechende Funktionalitaet
        ## im Regelgeraet eingebaut ist.
        ## OFFSET = Offset zur Einsortierung der Daten eines Typ s
        self.payload_regex = re.compile("(?P<id>B8|B9|A9|AB|B7)(?P<busnr>[0-9a-fA-F]{2})(?P<data_type>[0-9a-fA-F]{2})(?P<offset>[0-9a-fA-F]{2})(?P<data>(?:[0-9A-F]{12})+)")

        self.payload_regexes = {
            "A7" : re.compile("(?P<id>A7)(?P<busnr>[0-9a-fA-F]{2})(?P<data_type>[0-9a-fA-F]{2})(?P<offset>[0-9a-fA-F]{2})(?P<data>(?:[0-9A-F]{2}))"),
            "A8" : re.compile("(?P<id>A8)(?:(?P<busnr>[0-9a-fA-F]{2})(?P<data>(?:[0-9A-F]{12}))$|[8-9a-fA-F][0-9a-fA-F]{13}(?P<version_vk>[0-9a-fA-F]{2})(?P<version_nk>[0-9a-fA-F]{2}))"),
            "AE" : re.compile("(?P<id>AE)(?P<busnr>[0-9a-fA-F]{2})(?P<data>[0-9A-F]{8})"), ## Fehlerstatus
            "AF" : re.compile("AF(?P<bustime>[0-9a-fA-F]{12}|FF)") ## Uhrzeit Datum
        }
        ## Als Endekennung fuer das abgefragte Regelgeraet oder falls keine Daten vorhanden sind, wird der
        ## nachfolgende String
        ## 0xAC <ECOCAN-BUS-Adresse> gesendet  Endekennung bei A2<busnr> und bei B4<busnr>
        ## 0xAA <ECOCAN-BUS-Adresse> gesendet  Endekennung bei A1<busnr>
        ## 0xA8 0x80+adr < Seriennummer > <version vorkomma> <version nachkomma> Endekennung bei A100
        ##  Da A8 auch als normale Antwort kommt, muss auf A8[89a-fA-F]? abgefragt werden
        self.directmode_finish_regex = re.compile("(AC|AA|AD)(?P<busnr>[0-9a-fA-F]{2})")
        #self.directmode_finish_AD_regex = re.compile("AD(?P<busnr>[0-9a-fA-F]{2})(?P<data_type>[0-9a-fA-F]{2})(?P<offset>[0-9a-fA-F]{2})(?P<data>(?:[0-9A-F]{12}))")

        ##
        ## 1.Byte Sekunden (0-59)
        ## 2.Byte Minuten (0-59)
        ## 3.Byte Stunden / Sommerzeit
        ##      Bit 1-5 Stunden
        ##      Bit 6 intern
        ##      Bit 7 Sommerzeit (1=Sommerzeit)
        ##      Bit 8 Funkuhr (1=ist Funkuhrzeit)
        ## 4.Byte Tag (1-31)
        ## 5.Byte Monat / Wochentag
        ##      Bit 1-4 Monat
        ##      Bit 5-7 Wochentag
        ##      Bit 8 Funkuhrempfang zugelassen
        ## 6.Byte Jahr (89-188) > 100 20xx sonst 19xx
        ##
        ## Consumer Thread der Nachrichten an das Buderus Geraet schickt
        self.buderus_queue_thread = threading.Thread(target=self._send_to_buderus_consumer,name='hs_buderus_consumer')
        self.buderus_queue_thread.start()
        ## jetzt zum MOXA verbinden
        self.connect()
    def readconfig(self,configstring):
        ## config einlesen
        import re
        for (option,value) in re.findall("(\w+)=(.*?)(?:\*|$)", configstring ):
            option = option.lower()
            _configoption = self.config.get(option)
            _configtype = type(_configoption)
            ## wenn es den Wert nicht gibt
            if _configtype == type(None):
                self.log("unbekannte Konfig Option %s=%s" % (option,value), severity="error" )
                continue
            ## versuchen Wert im config string zum richtigen Type zu machen
            try:
                _val = _configtype(value)
                self.config[option] = _val
                #self.debug("Konfig Option %s=%s empfangen" % (option,value ), 5 )
            except ValueError:
                self.log("falscher Wert bei Konfig Option %s=%s (erwartet %r)" % (option,value, _configtype ), severity="error" )
                pass
    def time_to_bustime(self,set_time,funkuhr=0):
        return ("{0:02x}{1:02x}{2:02x}{3:02x}{4:02x}{5:02x}".format(
            set_time[5], ## Sekunden
            set_time[4], ## Minuten
            set_time[3] + (set_time[8] << 6) + (funkuhr << 7) , ## Stunden + Bit 7 Sommerzeit + Bit 8 Funkuhr
            set_time[2], ## Tag
            set_time[1] + ((set_time[6] + 1) << 4), ## Bit 1-4 Monat + Bit 5-7 (Wochentag +1)
            set_time[0] - 1900 ## Jahr -1900
        )).upper()
    def bustime_to_time(self,bustime):
        import binascii
        bustime = bustime.lstrip("AF")
        _bustime = [ ord(x) for x in binascii.unhexlify(bustime) ]
        return [
            (_bustime[5] + 1900), ## Jahr
            (_bustime[4] & 0xf), ## Monat
            _bustime[3], ## Tag
            _bustime[2] & 0x1f, # Stunden
            _bustime[1], ## Minuten
            _bustime[0], ## Sekunden
            (_bustime[4] >> 4 & 0x7) -1 , ## Wochentag
            0,
            -1 ##_bustime[2] >> 6 & 0x1 ## Sommerzeit ##FIXME## Time unknown
        ]
    def device_addresses(self,msg):
        _ret = []
        _addresses = map(lambda x: x=="1",bin(int(msg,16))[2:][::-1])
        for _addr in xrange(len(_addresses)):
            if _addresses[_addr]:
                _ret.append(_addr)
        return _ret
    def debug(self,msg,lvl=8):
        ## wenn debuglevel zu klein gleich zurueck
        if self.config.get("debug") == 0:
            return
        import time
        ## FIXME sollte spaeter gesetzt werden
        if lvl < 10 and lvl <= (self.config.get("debug")):
          self.log(msg,severity='debug')
        if (self.config.get("debug") == 10):
          print "%s DEBUG-12264: %r" % (time.strftime("%H:%M:%S"),msg,)
    def connect(self):
        ## _connect als Thread starten
        import threading
        self._moxa_thread = threading.Thread(target=self._connect,name='Buderus-Moxa-Connect')
        self._moxa_thread.start()
    def _send_to_buderus_consumer(self):
        import select,time
        while True:
            ## wenn noch keine Verbindung
            if not self.sock:
                self.debug("Socket nicht bereit ... warten")
                ## 1 Sekunden auf Socket warten
                time.sleep(1)
                continue
            ## solange noch ein direkt mode Befehlt austeht, darf kein neuer geschickt werden.
            if self.get_direct_waiting():
                continue
            ## naechste payload aus der Queue holen
            msg = self._buderus_message_queue.get()
            ## nach gueltigen zu sendener payload suchen
            _cmdid = msg[:2]
            _direct_mode_regex = self.directmode_regexes.get(_cmdid,self.directmode_regex)
            _direct_mode = _direct_mode_regex.search(msg)
            ## wenn keine gueltige SENDE payload
            if not _direct_mode:
                self.log("ungueltige sende Nachricht %r" % (msg,) )
                continue
            if _cmdid in [ "B1","B2"]:
                _busnr = _cmdid
            else:
                _busnr = _direct_mode.group("busnr")
            if self.config.get("readonly"):
                if _cmdid == "B0":
                    self.log("schreiben auf den Bus deaktiviert, Payload verworfen",severity="warn")
                    continue
                if _cmdid == "B2" and not self.config.get("writetime"):
                    self.log("schreiben der Uhrzeit deaktiviert, Payload verworfen",severity="warn")
                    continue
            ## Wenn eine direct-mode anfrage
            if _cmdid in ["A0","A1","A2","A3","B3","B4"]:
                if _busnr not in self.waiting_direct_bus:
                    ## busnr zur liste auf Antwort wartender hinzu
                    self.add_direct_waiting(_busnr)
                else:
                    ## Bus wird schon abgefragt
                    continue
            self._buderus_data_lock.acquire()
            self.debug("sende Queue exklusiv lock erhalten")
            try:
                ## wenn wir nicht schon im directmode sind oder nicht auf den directmode schalten konnten
                if not self.is_directmode():
                    if not self.set_directmode(True):
                        ## payload verworfen und loop
                        continue
                ## payload per 3964R versenden
                self._send3964r(msg)
                ## gucken ob wir den directmode noch brauchen
                self.check_directmode_needed()
            finally:
                self._buderus_data_lock.release()
                self.debug("sende Queue exklusiv lock released")
    def add_direct_waiting(self,busnr):
        ## busnr zur liste zu erwartender Antworten hinzufuegen
        try:
            self.directmode_lock.acquire()
            self.waiting_direct_bus.append(busnr)
        finally:
            self.directmode_lock.release()
    def remove_direct_waiting(self,busnr=None):
        ## busnr von der Liste der zu erwartetenden Antworten entfernen
        try:
            self.directmode_lock.acquire()
            ## wenn keine busnr uebergeben wurde, dann alle entfernen
            if not busnr:
                ## Flush
                self.waiting_direct_bus =[]
                self._is_directmode = False
            ## wenn die zu entfernenden busnr in der liste ist, entfernen
            elif busnr in self.waiting_direct_bus:
                self.waiting_direct_bus.remove(busnr)
        finally:
            self.directmode_lock.release()
    def get_direct_waiting(self):
        ## threadsicheres abfragen der zu erwartenden Antworten
        try:
            self.directmode_lock.acquire()
            return self.waiting_direct_bus
        finally:
            self.directmode_lock.release()
    def is_directmode(self):
        ## threadsicheres abfragen von directmode
        try:
            self.directmode_lock.acquire()
            return self._is_directmode
        finally:
            self.directmode_lock.release()
    def check_directmode_needed(self):
        import time
        ## Die Abfrage der gesamten Monitordaten braucht nur zu Beginn oder nach einem Reset zu erfolgen.
        ## Nach erfolgter Abfrage der Monitordaten sollte wieder mit dem Kommando 0xDC in den "Normal-Modus"
        ## zurueckgeschaltet werden.
        self.debug("check Directmode",lvl=7)
        ## wenn direct mode nicht an ist, dann gleich zurueck
        if not self.is_directmode():
            self.debug("kein Directmode",lvl=7)
            return
        ## wenn die Sendewarteschlange leer ist und keine Antworten(AC<busnr>) mehr von einem A2<busnr> erwartet werden,
        ## dann directmode ausschalten
        if (self._buderus_message_queue.empty() and not self.get_direct_waiting()):
            self.debug("deaktiviere Directmode",lvl=7)
            self.set_directmode(False)
        else:
            self.debug("check nicht Directmode",lvl=7)
    def set_directmode(self,mode):
        ## Bei dem Kommunikationsmodul wird zwischen einem "Normal-Modus" und einem "Direkt-Modus"
        ## unterschieden.
        ## "Normal-Modus" Bei diesem Modus werden laufend alle sich aendernden Monitorwerte
        ## sowie Fehlermeldungen uebertragen.
        ## "Direkt-Modus" Bei diesem Modus kann der aktuelle Stand aller bisher vom Regelgeraet
        ## generierten Monitordaten en Block abgefragt und ausgelesen werden.
        ## Mittels des Kommandos 0xDD kann von "Normal-Modus" in den "Direkt-Modus" umgeschaltet werden.
        ## In diesem Modus kann auf alle am ECOCAN-BUS angeschlossenen Geraete zugegriffen und es koennen
        ## geraeteweise die Monitorwerte ausgelesen werden.
        import time
        _setmode = "DC"
        if mode:
            _setmode = "DD"
        try:
            self.directmode_lock.acquire()
            _loop = 0
            ## FIXME: keine Ahnung ob wir das oefter als einmal versuchen oder nicht
            while not self._is_directmode == mode:
                if _loop == 2:
                    break
                # wenn der rueckgabewert vom Senden dem erwarteten mode erfolgreich ist, dann mode
                if self._send3964r(_setmode):
                    self._is_directmode = mode
                else:
                    self._is_directmode = not mode
                ## wenn kein erfolg dann 1 sekunde warten
                time.sleep(1)
                _loop += 1
            return (self._is_directmode == mode)
        finally:
            self.directmode_lock.release()
    def _send3964r(self,payload):
        ## returnwert erstmal auf False
        _ret = False
        try:
            ## auf Freigabe STX/DLE vom Socket warten
            if self.wait_for_ready_to_receive():
                ## Payload jetzt senden
                self.debug("jetzt payload %r senden" % (payload,) ,lvl=5)
                self.send_payload(payload)
                ## returnwert auf True
                _ret = True
            else:
                ## wenn kein DLE auf unser STX kam dann payload verwerfen
                self.debug("payload %r verworfen" % (payload,) ,lvl=4)
        except:
            ## Fehler auf die HS Debugseite
            self.MC.Debug.setErr(sys.exc_info(),"%r" % (payload,))
        return _ret
    ## send_out: Wert auf einen Ausgang senden
    ## Parameter out: Ausgang auf den gesendet werden soll analog zu AN[x]
    ## Parameter value: Wert der an den Ausgang gesendet werden soll
    def send_to_output(self,out,value):
        import time
        #out -= 1 ## Intern starten die Ausgaenge bei 0 und nicht bei 1
        ## Sendeintervall wird beachtet
        #if self.logik.SendIntervall == 0 or time.time() >= self.logik.Ausgang[out][0]:
            ## Wert an allen iKOs an den Ausgaengen setzen
        #    for iko in self.logik.Ausgang[out][1]:
        #        self.logik.MC.TagList.setWert(FLAG_EIB_LOGIK,iko, value)
            ## Wenn value nicht 0 / "" / None etc ist dann die Befehle ausfuehren
        #    if value:
        #        for cmd in self.logik.Ausgang[out][2]:
        #            cmd.execBefehl()
            ## Direkte Verbindungen und Connectoren
        #    for con in self.logik.Ausgang[out][3]:
        #        self.logik.MC.LogikList.ConnectList.append(con + [ value ])
            ## Wenn Sendeintervall gesetzt, naechste moegliche Ausfuehrungszeit setzen
        #    if self.logik.SendIntervall > 0:
        #        self.logik.Ausgang[out][0] = time.time() + self.logik.SendIntervall
            ## Ausgangswert auch in der Logik setzen
        #    self.logik.OutWert[out] = value
        print(value)
    def log(self,msg,severity='info'):
        self.send_to_output( 2, _msg )
    def incomming(self,msg):
        self.debug("incomming message %r" % (msg), lvl=5)
        ## mit * getrennte messages hinzufuegen
        for _msg in msg.split("*"):
            ## leerzeichen entfernen
            _msg = _msg.replace(' ','')
            ## _msg in die sende Warteschlange
            self._buderus_message_queue.put( _msg )
    def busnr_4byte_to_list(self,bytes):
        return (lambda addr: [x for x in xrange(len(addr)) if addr[x] ])(map(lambda x: x=="1",bin(int(bytes,16))[2:])[::-1])
    def parse_payload(self,payload):
        import time,binascii

        _cmdid = payload[:2]

        if _cmdid in ["A5","A6"]:
            self.debug("%s in Busgeraete: %r" % (_cmdid,self.busnr_4byte_to_list(payload[2:10])),lvl=6)
            return True

        _payload_regex = self.payload_regexes.get(_cmdid,self.payload_regex)
        ## nach gueltiger payload suchen
        _payload = _payload_regex.search(payload)
        ## wenn normal-mode oder direct mode antwort
        if _payload:
            if _cmdid == "A5":
                pass

            if _cmdid == "A6":
                pass

            ## wenn einen normal mode antwort mit Typ A7 kommt und der direktmode gerade an ist,
            ## dann ist der 60 Sekunden Timeout abgelaufen ohne die Daten rechtzeitig erhalten zu haben
            if _cmdid in ["A7", "B7"] and self.is_directmode():
                self.remove_direct_waiting()
                ## Der "Direkt-Modus" kann durch das Kommando 0xDC wieder verlassen werden.
                ## Ausserdem wird vom "Direkt-Modus" automatisch in den "Normal-Modus" zurueckgeschaltet, wenn fuer die
                ## Zeit von 60 sec kein Protokoll des "Direkt-Modus" mehr gesendet wird.
                self.log("Directmode timeout")
            if _cmdid == "A8" and self.is_directmode():
                if _payload.groupdict().get("busnr"):
                    self.log("Regelgeraet %s an ECOCAN BUS gefunden" % (  _payload.group("busnr") ) , severity="info")
                else:
                    self.log("ECOCAN BUS Version %r.%r gefunden" % ( ord(binascii.unhexlify(_payload.group("version_vk"))), ord(binascii.unhexlify(_payload.group("version_nk"))) ) ,severity="info")
                    self.remove_direct_waiting("00") # da mit "A000" eingeleitet ist, dann ist die Busnr "00", diese muss nun wieder geloescht werden
                    time.sleep( self.config.get('delaydirectendtime') )
                    self.check_directmode_needed()

            if _cmdid == "AF":
                _bustime = _payload.group("bustime")
                if _bustime == "FF":
                    self.log("Keine ECOBUS-Uhrzeit vorhanden")
                else:
                    _time = self.bustime_to_time(_bustime)
                    _diff = time.mktime(_time) - time.time()
                    self.log("ECOBUS-Uhrzeit empfangen: {0} (Differenz {1:.1f}sec)".format(time.strftime("%a %d.%m.%Y %H:%M:%S",_time),_diff))

            if _cmdid in ["A7","A9","AB","B7","B8","B9"]:
                ## Datentype
                _type = _payload.group("data_type")
                ## wenn wir das Geraet noch nicht gefunden hatten kurze Info ueber den Fund loggen
                if _type not in self.found_devices:
                    self.found_devices.append( _type )
                    (_devicename, _datalen) = self.data_types.get( _type, ("unbekannter Datentyp (%s)" % _type, 0) )
                    self.log("Datentyp '%s' an Regelgeraet %d gefunden" % ( _devicename, int(_payload.group("busnr")) ) , severity="info")
            return True
        else:
            ## wenn eine Endekennung AC|AA|AD<busnr> empfangen wurde, dann die busnr aus der liste fuer direct Daten entfernen und evtl direct_mode beenden
            _direct = self.directmode_finish_regex.search(payload)
            if _direct:
                _busnr = _direct.group("busnr")
                ## bus von der liste auf antwort wartender im direct mode entfernen
                self.remove_direct_waiting(_busnr)
                #self.log("BusNr %s geloescht" % ( repr(_busnr) ) ,severity="info")
                ## Wenn ein AC<busnr> gekommen ist, wird ggf. die Sende Richtung geaendert, was zu Initialisierungskonflikten fuehren kann
                time.sleep( self.config.get('delaydirectendtime') )
                self.check_directmode_needed()
                if _cmdid == "AD":
                    return True
            else:
                self.debug("NO Payload found",lvl=5)
        return False
    def wait_for_ready_to_receive(self):
        import select,time
        ## 3 versuche warten bis wir auf ein STX ein DLE erhalten
        for _loop in xrange(3):
            ## STX senden
            self.debug("STX senden")
            self.sock.send( self._constants['STX'] )
            self.debug("STX gesendet / warten auf DLE")
            ## auf daten warten, timeout ist QVZ
            _r,_w,_e = select.select( [ self.sock ],[],[], self._constants['QVZ'] )
            ## wenn kein timeout QVZ
            if self.sock in _r:
                # 1 Zeichen lesen
                data = self.sock.recv(1)
                ## wenn wir ein DLE empfangen
                if data == self._constants['DLE']:
                    self.debug("DLE empfangen")
                    ## erfolg zurueck
                    return True
                ## Wenn wir beim warten auf ein DLE ein STX der Gegenseite erhalten stellen wir unsere Sendung zurueck und lassen das andere Geraet seine Daten erstmal senden
                elif data == self._constants['STX']:
                    self.debug("STX empfangen Initialisierungskonflikt",lvl=5)
                    time.sleep(self._constants['ZVZ'])
                    ## DLE senden, dass wir Daten vom anderen Geraet akzeptieren senden
                    self.sock.send( self._constants['DLE'] )
                    self.debug("DLE gesendet")
                    ## eigentlich Funktion aus dem connect zum lesen der payload hier ausfuehren
                    self.read_payload()
                    ### danach loop und erneuter sende Versuch
                else:
                    self.debug("%r empfangen" % (data,),lvl=9 )
        self.debug("Nach 3x STX senden innerhalb QVZ kein DLE",lvl=5)
        return False
    ## Verbindung zum Moxa (gethreadet)
    def _connect(self):
        import time,socket,sys,select
        try:
            ## TCP Socket erstellen
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            ## IP:Port auslesen und dorthin verbinden
            try:
                _ip = '192.168.0.5'
                _port = '2001'
                self.sock.connect( ( _ip, int(_port) ) )
                self.log("Verbindung zu Netzwerkschnittstelle %s:%s hergestellt" % (_ip,_port))
            except (TypeError,ValueError):
                self.log("ungueltige IP:Port Kombination %r an Eingang 1" % self.device_connector, severity="error")
                return
            except socket.error as error:
                self.log("Verbindung zu Netzwerkschnittstelle %s:%s fehlgeschlagen" % (_ip,_port),severity="error")
                raise
            while True:
                # wenn keine Verbindung dann abbruch
                if not self.sock:
                    break
                _r,_w,_e = select.select( [ self.sock ],[],[], 10 )
                ## exklusiv lock
                if not self._buderus_data_lock.acquire(blocking=False):
                    ## wenn nicht erhalten lesen wir nicht vom socket, da die Daten fuer die Sende Queue sind
                    continue
                self.debug("empfang exklusiv lock erhalten")
                try:
                    ## wenn kein Timeout
                    if self.sock in _r:
                        ## wenn Daten da sind, ein zeichen lesen
                        data = self.sock.recv(1)
                        ## wenn keine Daten trotz select dann Verbindung abgebrochen
                        if not data:
                            self.debug("Verbindung abgebrochen",lvl=3)
                            break
                        ## wenn wir ein STX empfangen
                        if data == self._constants['STX']:
                            self.debug("STX empfangen sende DLE")
                            ## senden wir das DLE
                            self.sock.send( self._constants['DLE'] )
                            self.debug("DLE gesendet")
                            ## jetzt die eigentliche payload vom socket lesen
                            self.read_payload()
                        else:
                            self.debug("ungueltiges Zeichen %r empfangen" % (data,) ,lvl=4)
                finally:
                    ## den lock auf jedenfall relasen
                    self._buderus_data_lock.release()
                    self.debug("empfang exklusiv lock releasen")
        except:
            self.debug(sys.exc_info())
            ## 10 sekunden pause
            time.sleep(10)
        ## dann reconnect
        self.connect()
    ## STX = 0x02
    ## DLE = 0x10
    ## ETX = 0x03
    ## NAK = 0x15
    ## Die Steuerzeichen fuer die Prozedur 3964R sind der Norm DIN 66003 fuer den 7-Bit-Code entnommen. Sie
    ## werden allerdings mit der Zeichenlaenge 8 Bit uebertragen (Bit I7 = 0). Am Ende jedes Datenblocks wird zur
    ## Datensicherung ein Pruefzeichen(BCC) gesendet.
    ## Das Blockpruefzeichen wird durch eine exklusiv-oder-Verknuepfung ueber alle Datenbytes der
    ## Nutzinformation, inclusive der Endekennung DLE, ETX gebildet.
    def send_payload(self,payload):
        ## Senden mit der Prozedur 3964R
        ## -----------------------------
        ## Zum Aufbau der Verbindung sendet die Prozedur 3964R das Steuerzeichen STX aus. Antwortet das
        ## Peripheriegeraet vor Ablauf der Quittungsverzugzeit (QVZ) von 2 sec mit dem Zeichen DLE, so geht die
        ## Prozedur in den Sendebetrieb ueber. Antwortet das Peripheriegeraet mit NAK, einem beliebigen anderen
        ## Zeichen (ausser DLE) oder die Quittungsverzugszeit verstreicht ohne Reaktion, so ist der
        ## Verbindungsaufbau gescheitert. Nach insgesamt drei vergeblichen Versuchen bricht die Prozedur das
        ## Verfahren ab und meldet dem Interpreter den Fehler im Verbindungsaufbau.
        ## Gelingt der Verbindungsaufbau, so werden nun die im aktuellen Ausgabepuffer enthaltenen
        ## Nutzinformationszeichen mit der gewaehlten uebertragungsgeschwindigkeit an das Peripheriegeraet
        ## gesendet. Das Peripheriegeraet soll die ankommenden Zeichen in Ihrem zeitlichen Abstand ueberwachen.
        ## Der Abstand zwischen zwei Zeichen darf nicht mehr als die Zeichenverzugszeit (ZVZ) von 220 ms
        ## betragen.
        ## Jedes im Puffer vorgefundene Zeichen DLE wird als zwei Zeichen DLE gesendet. Dabei wird das Zeichen
        ## DLE zweimal in die Pruefsumme uebernommen.
        ## Nach erfolgtem senden des Pufferinhalts fuegt die Prozedur die Zeichen DLE, ETX und BCC als
        ## Endekennung an und wartet auf ein Quittungszeichen. Sendet das Peripheriegeraet innerhalb der
        ## Quittungsverzugszeit QVZ das Zeichen DLE, so wurde der Datenblock fehlerfrei uebernommen. Antwortet
        ## das Peripheriegeraet mit NAK, einem beliebigen anderen Zeichen (ausser DLE), einem gestoerten Zeichen
        ## oder die Quittungsverzugszeit verstreicht ohne Reaktion, so wiederholt die Prozedur das Senden des
        ## Datenblocks. Nach insgesamt sechs vergeblichen Versuchen, den Datenblock zu senden, bricht die
        ## Prozedur das Verfahren ab und meldet dem Interpreter den Fehler im Verbindungsaufbau.
        ## Sendet das Peripheriegeraet waehrend einer laufenden Sendung das Zeichen NAK, so beendet die
        ## Prozedur den Block und wiederholt in der oben beschriebenen Weise.
        import select,binascii
        ## 6 versuche

        ## Ungueltige Payload abfangen um exception zu verhindern
        if len(payload) % 2:
            self.debug("ungueltige Payloadlaenge",lvl=1)
            return

        for _loop in xrange(6):
            self.debug("exklusiv senden / versuch %d" % (_loop),lvl=6)
            ## checksumme
            _bcc = 0
            for _byte in binascii.unhexlify(payload):
                ## Byte an Geraet schicken
                self.sock.send( _byte )
                self.debug("Byte %r versendet" % (binascii.hexlify(_byte)),lvl=8 )
                ## Checksumme berechnen
                _bcc ^= ord(_byte)
                ## Wenn payload ein DLE ist
                if _byte == self._constants['DLE']:
                    ## dann in der payload verdoppeln
                    self.sock.send( _byte )
                    self.debug("Payload enthaellt DLE, ersetzt mit DLE DLE",lvl=7 )
                    ## doppeltes DLE auch in die Checksumme einrechenen
                    _bcc ^= ord(_byte)
            ## Abschluss der Prozedur 3964R durch senden von DLE ETX
            self.debug("Alle Daten gesendet, jetzt DLE und ETX")
            self.sock.send( self._constants['DLE'] )
            _bcc ^= ord( self._constants['DLE'] )
            self.sock.send( self._constants['ETX'] )
            _bcc ^= ord( self._constants['ETX'] )
            ## Berechnete Checksukmme
            self.debug("jetzt checksumme %r senden" % (_bcc) )
            self.sock.send( chr(_bcc) )
            ## auf daten warten, timeout ist Quittungsverzugszeit
            self.debug("warten auf DLE")
            _r,_w,_e = select.select( [ self.sock ],[],[], self._constants['QVZ'] )
            ## wenn nicht Quittingsverzugszeit
            if self.sock in _r:
                ## 1 zeichen lesen
                data = self.sock.recv(1)
                ## wenn empfangenes zeichen DLE ist
                if data == self._constants['DLE']:
                    self.debug("DLE erhalten")
                    self.debug("Daten %r erfolgreich gesendet" % (payload,),lvl=2)
                    return True
            self.debug("Kein DLE erhalten loop",lvl=6)
        self.debug("Nach 6x STX senden innerhalb QVZ kein DLE",lvl=1)
    def read_payload(self):
        ## Empfangen mit der Prozedur 3964R
        ## --------------------------------
        ## Im Ruhezustand, wenn kein Sendeauftrag und kein Warteauftrag des Interpreters zu bearbeiten ist, wartet
        ## die Prozedur auf den Verbindungsaufbau durch das Peripheriegeraet. Empfaengt die Prozedur ein STX und
        ## steht ihr ein leerer Eingabepuffer zur Verfuegung, wird mit DLE geantwortet.
        ## Nachfolgende Empfangszeichen werden nun in dem Eingabepuffer abgelegt. Werden zwei aufeinander
        ## folgende Zeichen DLE empfangen, wird nur ein DLE in den Eingabepuffer uebernommen.
        ## Nach jedem Empfangszeichen wird waehrend der Zeichenverzugszeit (ZVZ) auf das naechste Zeichen
        ## gewartet. Verstreicht die Zeichenverzugszeit ohne Empfang, wird das Zeichen NAK an das
        ## Peripheriegeraet gesendet und der Fehler an den Interpreter gemeldet.
        ## Mit erkennen der Zeichenfolge DLE, ETX und BCC beendet die Prozedur den Empfang und sendet DLE
        ## fuer einen fehlerfrei (oder NAK fuer einen fehlerhaft) empfangenen Block an das Peripheriegeraet.
        ## Treten waehrend des Empfangs uebertragungsfehler auf (verlorenes Zeichen, Rahmenfehler), wird der
        ## Empfang bis zum Verbindungsabbau weitergefuehrt und NAK an das Peripheriegeraet gesendet. Dann wird
        ## eine Wiederholung des Blocks erwartet. Kann der Block auch nach insgesamt sechs Versuchen nicht
        ## fehlerfrei empfangen werden, oder wird die Wiederholung vom Peripheriegeraet nicht innerhalb der
        ## Blockwartezeit von 4 sec gestartet, bricht die Prozedur 3964R den Empfang ab und meldet den Fehler an
        ## den Interpreter.
        import select,binascii,time
        ## 6 versuche sind erlaubt
        for _loop in xrange(6):
            self.debug("exklusiv lesen / versuch %d" % (_loop),lvl=8)
            ## speicher fuer das zuletzt empfangene zeichen um DLE DLE bzw DLE ETX zu erkennen
            _lastchar = ""
            ## checksumme
            _bcc = 0
            ## eigentliche Payload
            _payload = []
            ## nach erhalten von DLE ETX (Ende der uebermittlung) wird auf True gesetzt, somit ist das naechste Zeichen die gesendetet Checksumme
            _wait_for_checksum = False
            ## Timer fuer die Blockwartezeit
            _bwz_timer = time.time() + self._constants['BWZ']
            while True:
                ## auf dem socket auf Veraenderung warten
                _r,_w,_e = select.select( [ self.sock ],[],[], self._constants['ZVZ'] )
                ## wenn obiger select mit Timeout von Zeichenverzugszeit
                if not self.sock in _r:
                    ## wenn schon Daten da nur zeichenverzugszeit/ wenn keine Daten dann Blockwartezeit
                    if len(_payload) > 0 or _bwz_timer <= time.time():
                        ## kein zeichen innerhalb ZVZ bzw BWZ
                        self.debug("abbruch ZVZ oder BWZ",lvl=1)
                        ## NAK an Geraet senden
                        self.sock.send( self._constants['NAK'] )
                        ## gegenseite zeit geben
                        time.sleep( self._constants['ZVZ'] )
                        ## abruck der while Schleife zurueck in connect
                        break
                    ## wenn noch keine daten und blockwartezeit nicht ueberschritten
                    else:
                        self.debug("weiter warten auf daten noch kein ZVZ/BWZ timeout")
                        continue
                ## ein Zeichen lesen
                data = self.sock.recv(1)
                ## wenn keine Daten auf Socket (Verbindungsabbruch)
                if not data:
                    self.debug("Keine Daten / verbindung verloren",lvl=3)
                    return
                ## wenn checksumme erwartet wird
                if _wait_for_checksum:
                    ## empfangene Checksumme
                    _bcc_recv = ord(data)
                    self.debug("berechnete checksumme = %.2x empfange checksumme = %.2x" % ( _bcc,_bcc_recv) )
                    ## wenn empfangene Checkumme der berechneten entspricht
                    if _bcc == _bcc_recv:
                        ## payload von Type List zum String machen und alle hex Zeichen als Grossbuchstaben
                        _hexpayload = "".join( _payload ).upper()
                        self.debug("Payload %r erfolgreich empfangen" % (_hexpayload),lvl=2)
                        ## DLE als Bestaetigung senden
                        self.sock.send( self._constants['DLE'] )
                        ## empfangene Payload analysieren
                        if self.parse_payload( _hexpayload ):
                            ## payload an Ausgang 1 senden
                            self.send_to_output(1, _hexpayload)
                        return
                    ## checksummen stimmen nicht ueberein
                    else:
                        self.debug("Checksum nicht korrekt %r != %r" % (_bcc, _bcc_recv) ,lvl=1)
                        ## NAK an geraet senden
                        self.sock.send( self._constants['NAK'] )
                        ## FIXME BREAK heisst nochmal in die 6 versuche oder return waere zurueck zum mainloop warten auf STX
                        break
                ## checksum von jedem packet berechnen
                _bcc ^= ord(data)
                ## wenn 2mal DLE hintereinander bcc berechnen aber nur eins zum packet
                if data == _lastchar == self._constants['DLE']:
                    self.debug("entferne doppeltes DLE")
                    ## loeschen damit bei DLE DLE DLE ETX nicht das 3te DLE auch wieder entfernt wird
                    _lastchar = ""
                    continue
                ## WENN DLE ETX dann Ende
                if _lastchar == self._constants['DLE'] and data ==  self._constants['ETX']:
                    self.debug("DLE/ETX empfangen warte auf checksumme")
                    _wait_for_checksum = True
                    ## letztes DLE entfernen denn das gehoert nicht zur payload sondern zum 3964R
                    _payload = _payload[:-1]
                    continue
                ## daten zum packet hinzu
                _payload.append( binascii.hexlify(data) )
                self.debug("Daten %r empfangen" % (binascii.hexlify(data)),lvl=7)
                ## letztes zeichen speichern
                _lastchar = data

def main():
    print("ANFANG!")
    bud = buderus_connect()
    bud.debug("Test")
    print("ENDE")

if __name__ == "__main__":
    main()
