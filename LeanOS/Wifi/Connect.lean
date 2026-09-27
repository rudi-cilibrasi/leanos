import LeanOS.Wifi.Driver
import LeanOS.Wifi.DevCcmp
import LeanOS.Wifi.DevDhcp

/-
Complete station bring-up for the Qotom card: associate with a QUAIL access
point, run the WPA2 4-way handshake, then obtain an IPv4 lease with DHCP
over CCMP. The DHCP phase follows the simulated flow of
`tests/WifiDhcpSim.lean`, with frames sent through the hardware TX
descriptor path.
-/
namespace LeanOS.Wifi.Connect

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.NPhy LeanOS.Wifi.Driver

def plainBuf : UInt32 := 0x4000
def txPnAt : UInt32 := 0x0C00
def leasedIpAt : UInt32 := 0x0C08

namespace Fail
def noReply : UInt32 := 0x7E01
def nak : UInt32 := 0x7E02
def encap : UInt32 := 0x7E03
end Fail

namespace Tag
def discoverSent : UInt32 := 0x0E01
def offer : UInt32 := 0x0E02
def requestSent : UInt32 := 0x0E03
def ack : UInt32 := 0x0E04
def leasedIp : UInt32 := 0x0E05
def dropped : UInt32 := 0x0E06
def router : UInt32 := 0x0E07
def subnet : UInt32 := 0x0E08
def lease : UInt32 := 0x0E09
def kicked : UInt32 := 0x0E20
def candidate : UInt32 := 0x0E21
def decap : UInt32 := 0x0E22
def bodyLen : UInt32 := 0x0E23
def body : UInt32 := 0x0E24
def parse : UInt32 := 0x0E25
def dump : UInt32 := 0x0E26
end Tag

/-- `sendMpdu` with the MPDU length in register r12 (run-time length). -/
def sendMpduR (c : LeanOS.Wifi.Tx.TxConfig) (fifo : UInt32) : ProgM Unit := do
  li 11 (Mlme.txMpdu - 118)
  LeanOS.Wifi.Tx.emitTxHeader c 11 12
  emit (.memLoad 2 8 11 76)
  addi 12 118
  Mac.pioTx fifo 11 12
  LeanOS.Wifi.Tx.readTxStatus 8 2000 50
  print 0x0E10 0
  print 0x0E11 1
  print 0x0E12 2
  print 0x0E13 3

/-- Build a plaintext frame with `build` (length in r0) at `plainBuf`, protect
it with the TK into `txMpdu`, and transmit it from the best-effort FIFO. -/
def sendProtected (C : DevCcmp.CcmpLib) (c : LeanOS.Wifi.Tx.TxConfig) (build : ProgM Unit) :
    ProgM Unit := do
  build
  mov 2 0
  DevCcmp.callEncap C (.imm plainBuf) (.reg 2) (.imm Mlme.txMpdu) (.imm Handshake.tkAt)
    (.imm txPnAt) (.imm 0)
  let ok ← newLabel
  emit (.branch .ne 0 (.imm 0) ok)
  fail Fail.encap
  place ok
  mov 12 0
  sendMpduR c 1

/-- Receive until a protected data frame from the BSSID decrypts (TK or GTK)
to a DHCP reply of our transaction, for at most `frames` microseconds of
TSF time; r0 = DHCP message type. -/
def waitDhcpWith (L : DevCrypto.Lib) (mgmt : LeanOS.Wifi.Tx.TxConfig) (C : DevCcmp.CcmpLib)
    (D : DevDhcp.DhcpLib) (frames tries : UInt32) (soft : Bool) : ProgM Unit := do
  let top ← newLabel
  let skip ← newLabel
  let give ← newLabel
  let done ← newLabel
  -- Deadline in microseconds of the MAC's TSF timer (tsf_timerlow, 0x180):
  -- wall-clock bounded, independent of executor speed and channel load.
  li 0 0
  r32 6 0x180
  emit (.memStore 4 0 (leasedIpAt + 4) (.reg 6))
  place top
  r32 6 0x180
  li 0 0
  emit (.memLoad 4 7 0 (leasedIpAt + 4))
  emit (.alu .sub 6 (.reg 7))
  emit (.branch .geu 6 (.imm frames) give)
  Mlme.rxFrame tries
  emit (.branch .ltu 5 (.imm (24 + 16 + 4)) skip)
  -- diagnostics: deauthentication/disassociation addressed to us
  li 0 0
  emit (.memLoad 1 1 0 Mlme.rxMpdu)
  let notMgmtKill ← newLabel
  let isKill ← newLabel
  emit (.branch .eq 1 (.imm 0xA0) isKill)       -- disassociation
  emit (.branch .eq 1 (.imm 0xC0) isKill)       -- deauthentication
  emit (.jump notMgmtKill)
  place isKill
  Mlme.matchBytes (Mlme.rxMpdu + 4) Mlme.ourMac notMgmtKill
  li 0 0
  emit (.memLoad 2 2 0 (Mlme.rxMpdu + 24))
  print Tag.kicked 2
  place notMgmtKill
  li 0 0
  emit (.memLoad 1 1 0 Mlme.rxMpdu)
  andi 1 0x0C
  emit (.branch .ne 1 (.imm 0x08) skip)
  emit (.memLoad 1 1 0 (Mlme.rxMpdu + 1))
  andi 1 0x40
  let prot ← newLabel
  emit (.branch .ne 1 (.imm 0) prot)
  -- unprotected data: a retransmitted EAPOL message 3 from the BSSID?
  Mlme.matchScratch (Mlme.rxMpdu + 10) Mlme.bssidAt 6 skip
  li 0 0
  emit (.memLoad 1 1 0 Mlme.rxMpdu)
  li 7 (Mlme.rxMpdu + 24)
  andi 1 0x80
  let plainHdr ← newLabel
  emit (.branch .eq 1 (.imm 0) plainHdr)
  li 7 (Mlme.rxMpdu + 26)
  place plainHdr
  emit (.memLoad 1 1 7 6)
  emit (.branch .ne 1 (.imm 0x88) skip)
  emit (.memLoad 1 1 7 7)
  emit (.branch .ne 1 (.imm 0x8E) skip)
  addi 7 8
  mov 8 5
  emit (.alu .add 8 (.imm Mlme.rxMpdu))
  emit (.alu .sub 8 (.reg 7))
  emit (.alu .sub 8 (.imm 4))
  Handshake.answerMsg3 L (sendMpdu mgmt 3)
  emit (.jump skip)
  place prot
  Mlme.matchScratch (Mlme.rxMpdu + 10) Mlme.bssidAt 6 skip
  mov 2 5
  emit (.alu .sub 2 (.imm 4))
  li 0 0
  emit (.memLoad 1 5 0 Handshake.gtkIdAt)
  li 0 0
  emit (.memLoad 4 3 0 (Mlme.rxMpdu + 4)); print Tag.candidate 3
  DevCcmp.callDecap C (.imm Mlme.rxMpdu) (.reg 2) (.imm Handshake.tkAt) (.imm Handshake.gtkAt)
    (.reg 5)
  print Tag.decap 0
  emit (.branch .eq 0 (.imm 0) skip)
  print Tag.bodyLen 2
  emit (.memLoad 4 3 1 6); print Tag.body 3        -- ethertype + IP version
  emit (.memLoad 4 3 1 16); print Tag.body 3       -- protocol/checksum
  -- dump UDP bodies (IPv4 protocol 17) of plausible DHCP size
  let noDump ← newLabel
  emit (.memLoad 1 3 1 17)
  emit (.branch .ne 3 (.imm 17) noDump)
  emit (.branch .ltu 2 (.imm 200) noDump)
  li 4 0
  let dl ← newLabel
  place dl
  mov 3 1
  emit (.alu .add 3 (.reg 4))
  emit (.memLoad 4 3 3 0)
  print Tag.dump 3
  addi 4 4
  emit (.branch .ltu 4 (.reg 2) dl)
  place noDump
  DevDhcp.callParse D (.reg 1) (.reg 2)
  print Tag.parse 0
  emit (.branch .ne 0 (.imm 0) done)
  place skip
  emit (.jump top)
  place give
  if soft then li 0 0 else fail Fail.noReply
  place done

def waitDhcp (L : DevCrypto.Lib) (mgmt : LeanOS.Wifi.Tx.TxConfig) (C : DevCcmp.CcmpLib)
    (D : DevDhcp.DhcpLib) (frames tries : UInt32) : ProgM Unit :=
  waitDhcpWith L mgmt C D frames tries false

/-- Like `waitDhcp`, but returns r0 = 0 instead of failing when no reply
arrives within `frames` frames. -/
def waitDhcpSoft (L : DevCrypto.Lib) (mgmt : LeanOS.Wifi.Tx.TxConfig) (C : DevCcmp.CcmpLib)
    (D : DevDhcp.DhcpLib) (frames tries : UInt32) : ProgM Unit :=
  waitDhcpWith L mgmt C D frames tries true

/-- Associate, authenticate with WPA2-PSK and lease an address. -/
def connectDhcp (fw : Firmware) (cfg : PhyCfg) (bssid pmk : ByteArray) : ProgM Unit := do
  let L ← DevCrypto.install
  let C ← DevCcmp.install L
  let D ← DevDhcp.install
  bringUp
  ucodeStart fw
  Mac.coreInitTail
  Mac.bandInit fw (phyInitFull cfg)
  LeanOS.Wifi.Tx.txSetup cfg (ByteArray.mk Mlme.ourMac.data) bssid
  Mac.enableMacPromisc
  Mlme.putBytes "bssid" Mlme.bssidAt bssid
  let mgmt := LeanOS.Wifi.Tx.TxConfig.ofPhy cfg .cck1
  let data := LeanOS.Wifi.Tx.TxConfig.ofPhy cfg .cck1 1
  Mlme.authAssoc (sendMpdu mgmt 3) 3000
  Handshake.fourWay L pmk LeanOS.Wifi.Ieee80211.wpa2PskCcmpRsnIe (sendMpdu mgmt 3) 3000
  Handshake.copyFrom 0 (Handshake.entropy2At + 12) DevDhcp.xidAt 4
  delay 200000
  let gotOffer ← newLabel
  for _ in [0:3] do
    sendProtected C data (DevDhcp.callDiscover D (.imm plainBuf))
    printImm Tag.discoverSent 0
    waitDhcpSoft L mgmt C D 5000000 1000
    emit (.branch .eq 0 (.imm 2) gotOffer)
  fail Fail.noReply
  place gotOffer
  li 0 0
  emit (.memLoad 4 1 0 DevDhcp.yiaddrAt)
  print Tag.offer 1
  sendProtected C data (DevDhcp.callRequest D (.imm plainBuf))
  printImm Tag.requestSent 0
  let gotAck ← newLabel
  waitDhcp L mgmt C D 5000000 1000
  emit (.branch .eq 0 (.imm 5) gotAck)
  fail Fail.nak
  place gotAck
  printImm Tag.ack 0
  li 0 0
  emit (.memLoad 4 1 0 DevDhcp.yiaddrAt)
  emit (.memStore 4 0 leasedIpAt (.reg 1))
  print Tag.leasedIp 1
  emit (.memLoad 4 1 0 DevDhcp.routerAt); print Tag.router 1
  emit (.memLoad 4 1 0 DevDhcp.subnetAt); print Tag.subnet 1
  emit (.memLoad 4 1 0 DevDhcp.leaseAt); print Tag.lease 1
  printImm Bcm43224.Tag.done 0
  halt

end LeanOS.Wifi.Connect
