namespace LeanOS.Experiment

@[export leanos_transition]
def transition (state command : UInt64) : UInt64 :=
  state ^^^ command

end LeanOS.Experiment
