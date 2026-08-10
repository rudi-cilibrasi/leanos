import LeanOS.VTdBootPlan

open LeanOS.VTdBootPlan

-- A surprise present context entry in the live-unit read must be rejected by
-- the generated snapshot validator; claiming it validates is false.
example : (match compile sampleInput with
    | .ok plan =>
        (validateDecodedUnit plan
          { expectedDecodedUnit plan with
            contextWords := (expectedDecodedUnit plan).contextWords.set 0
              (UInt64.ofNat (12 * 4096 + 1)) }).isOk
    | .error _ => false) = true := by native_decide
