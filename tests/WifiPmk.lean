import LeanOS.Wifi.Pbkdf2

/-! Hosted helper: print the WPA2-PSK PMK for the SSID and passphrase given in
the environment variables `LEANOS_WIFI_SSID` and `LEANOS_WIFI_PSK`, for
comparison with `wpa_passphrase <ssid> <passphrase>`.

The passphrase is read only from the environment and never printed. -/

open LeanOS.Wifi

def main : IO UInt32 := do
  let ssid? ← IO.getEnv "LEANOS_WIFI_SSID"
  let psk? ← IO.getEnv "LEANOS_WIFI_PSK"
  match ssid?, psk? with
  | some ssid, some psk =>
    let ssidBytes := ssid.toUTF8
    let pskBytes := psk.toUTF8
    if ssidBytes.size == 0 || ssidBytes.size > 32 then
      IO.eprintln "LEANOS_WIFI_SSID must be 1..32 bytes"
      return 2
    if pskBytes.size < 8 || pskBytes.size > 63 then
      IO.eprintln "LEANOS_WIFI_PSK must be an 8..63 character passphrase"
      return 2
    IO.println s!"ssid={ssid}"
    IO.println s!"psk={Bytes.toHex (Pbkdf2.pmkOfPassphrase pskBytes ssidBytes)}"
    return 0
  | _, _ =>
    IO.eprintln "set LEANOS_WIFI_SSID and LEANOS_WIFI_PSK"
    return 2
