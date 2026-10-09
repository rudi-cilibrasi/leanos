import LeanOS.SecurityClaims

open LeanOS

/- Release does not scrub: a reclaimed frame keeps its previous holder's bytes
until the server grants it again, and only that grant scrubs it.  A weakened
scrub claim in which reclaim itself zeroes the frame (so that publishing could
skip the scrub) must not follow from SC-FRAME-SERVER-SCRUB, which only says
reclaim leaves the bytes unchanged. -/
example (sys : FrameServer.System) (caller client : Capability.SubjectId)
    (frame : FrameAllocator.FrameId) (offset : Nat) (_hoffset : offset < FrameScrub.frameBytes) :
    (FrameServer.decide sys caller (.reclaim client frame)).1.bytes frame offset =
      FrameScrub.initialByte := by
  exact (SecurityClaims.frame_server_scrub sys caller client frame 3).2.1
