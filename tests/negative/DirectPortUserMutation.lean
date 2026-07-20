import LeanOS.DirectPortIO

open LeanOS DirectPortIO

-- A user-origin request cannot be used to prove any modeled device mutation.
example state live request :
    (executeUser state live request).state.devices ≠ state.devices := by
  exact user_request_preserves_device_state state live request
