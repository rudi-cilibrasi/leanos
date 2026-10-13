import LeanOS.Oracle.Vector
import LeanOS.NotifyReply
import LeanOS.UserCopyPolicy
import LeanOS.ConsoleServer
import LeanOS.EndpointDirectory
import LeanOS.FaultHandler
import LeanOS.KeyboardEcho
import LeanOS.TimerServer
import LeanOS.FrameServer

/-!
# Oracle corpus: user-level services and devices

The rows of notification and reply capabilities, user-copy range checks, the
console server, the endpoint directory, the fault handler, keyboard-echo device
authority, the timer server, and the frame server.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

private def notifyReplyEvent (id : String) (script step operation subject : UInt64) : Vector :=
  { id, adapter := "NotifyReply.event", words := [script, step, operation, subject],
    expected := NotifyReply.notifyReplyEvent script step operation subject }

/-- A user-copy range check. The expected word is `UserCopy.validate` on the
boot mapping state (`UserCopyPolicy.model`), not the generated adapter. -/
private def userCopy (id : String) (flags start length : UInt64) : Vector :=
  let text := UserCopyPolicy.bootText
  let stack := UserCopyPolicy.bootStack
  let top := UserCopyPolicy.bootStackTop
  { id, adapter := "UserCopy.policy", words := [flags, start, length, text, stack, top],
    expected := UserCopyPolicy.model flags start length text stack top }

private def consoleAuthorize (id : String) (subject operation : UInt64) : Vector :=
  { id, adapter := "ConsoleServer.authorize", words := [subject, operation],
    expected := ConsoleServer.consoleAuthorize subject operation }

private def directoryResolve (id : String) (registered held : UInt64) : Vector :=
  { id, adapter := "EndpointDirectory.resolve", words := [registered, held],
    expected := EndpointDirectory.directoryResolve registered held }

private def faultHandlerRoute (id : String) (event vector subject word : UInt64) : Vector :=
  { id, adapter := "FaultHandler.route", words := [event, vector, subject, word],
    expected := FaultHandler.faultHandlerRoute event vector subject word }

private def deviceAuthorize (id : String) (subject device : UInt64) : Vector :=
  { id, adapter := "KeyboardEcho.deviceAuthorize", words := [subject, device],
    expected := KeyboardEcho.deviceAuthorize subject device }

private def timerServerDecide (id : String) (event subject word : UInt64) : Vector :=
  { id, adapter := "TimerServer.decide", words := [event, subject, word],
    expected := TimerServer.timerServerDecide event subject word }
private def frameServerCheck (id : String) (op view usage limit requested held : UInt64) :
    Vector :=
  { id, adapter := "FrameServer.check", words := [op, view, usage, limit, requested, held],
    expected := FrameServer.frameServerCheck op view usage limit requested held }

private def frameServerView (id : String) (op index poolSize holder client free : UInt64) :
    Vector :=
  { id, adapter := "FrameServer.view", words := [op, index, poolSize, holder, client, free],
    expected := FrameServer.frameServerView op index poolSize holder client free }

/-- Notification and reply-capability edges (#471): the machine scenario,
the rejected edges (signal without the right, copying a reply capability,
reply after the caller terminated, a double reply), and off-script refusals. -/
def notifyReplyVectors : List Vector := [
  notifyReplyEvent "notify-reply.wait-blocks" 0 0 2 2,
  notifyReplyEvent "notify-reply.signal" 0 1 1 1,
  notifyReplyEvent "notify-reply.wait-wakes" 0 2 2 2,
  notifyReplyEvent "notify-reply.call" 0 3 3 1,
  notifyReplyEvent "notify-reply.reply" 0 4 4 2,
  notifyReplyEvent "notify-reply.double-reply" 0 5 4 2,
  notifyReplyEvent "notify-reply.signal-without-right" 1 0 1 2,
  notifyReplyEvent "notify-reply.negative-call" 1 1 3 1,
  notifyReplyEvent "notify-reply.copy-reply" 1 2 5 2,
  notifyReplyEvent "notify-reply.caller-terminates" 1 3 6 1,
  notifyReplyEvent "notify-reply.reply-after-termination" 1 4 4 2,
  notifyReplyEvent "notify-reply.off-script-step" 0 9 4 2,
  notifyReplyEvent "notify-reply.unknown-script" 2 0 2 2]

/-- User-copy range checks (#478) on the boot layout: one text page at
0x29a000 and two stack pages at 0x29b000. Flags: bit 0 write, bit 1 current
lifetime, bits 8 and up the subject. -/
def userCopyPolicyVectors : List Vector := [
  userCopy "user-copy.zero-length" 0x102 0x29b000 0,
  userCopy "user-copy.stack-read" 0x102 0x29b000 16,
  userCopy "user-copy.stack-write" 0x103 0x29cff0 16,
  userCopy "user-copy.stack-top-unmapped" 0x102 0x29d000 1,
  userCopy "user-copy.straddles-stack-top" 0x102 0x29cff8 16,
  userCopy "user-copy.text-read" 0x102 0x29a000 1,
  userCopy "user-copy.text-write-read-only" 0x103 0x29a000 1,
  userCopy "user-copy.text-into-stack-write" 0x103 0x29aff8 16,
  userCopy "user-copy.too-long" 0x102 0x29b000 17,
  userCopy "user-copy.overflow" 0x102 0xfffffffffffffff9 16,
  userCopy "user-copy.end-at-2-pow-64" 0x102 0xfffffffffffffff8 8,
  userCopy "user-copy.noncanonical" 0x102 0x800000000000 1,
  userCopy "user-copy.wrong-subject" 0x202 0x29b000 1,
  userCopy "user-copy.stale" 0x100 0x29b000 1]

/-- Console-server authority decisions (#472): every subject (A 1, B 2,
server C 3) against every operation (send 1, console write 2, console read 3,
serve 4, receive 5), then codes outside the ABI. -/
def consoleAuthorizeVectors : List Vector := [
  consoleAuthorize "console-authorize.a-send" 1 1,
  consoleAuthorize "console-authorize.a-write" 1 2,
  consoleAuthorize "console-authorize.a-read" 1 3,
  consoleAuthorize "console-authorize.a-serve" 1 4,
  consoleAuthorize "console-authorize.a-receive" 1 5,
  consoleAuthorize "console-authorize.b-send" 2 1,
  consoleAuthorize "console-authorize.b-write" 2 2,
  consoleAuthorize "console-authorize.b-read" 2 3,
  consoleAuthorize "console-authorize.b-serve" 2 4,
  consoleAuthorize "console-authorize.b-receive" 2 5,
  consoleAuthorize "console-authorize.server-send" 3 1,
  consoleAuthorize "console-authorize.server-write" 3 2,
  consoleAuthorize "console-authorize.server-read" 3 3,
  consoleAuthorize "console-authorize.server-serve" 3 4,
  consoleAuthorize "console-authorize.server-receive" 3 5,
  consoleAuthorize "console-authorize.unknown-subject" 4 2,
  consoleAuthorize "console-authorize.zero-operation" 3 0,
  consoleAuthorize "console-authorize.unknown-operation" 3 6,
  consoleAuthorize "console-authorize.maximum-words" 0xffffffffffffffff
    0xffffffffffffffff]

/-- Endpoint-directory rights decisions (#485): an unregistered name, then a
registered name over every endpoint-rights word (send 1, receive 2, grant 4,
revoke 8), then words outside the four bits. -/
def directoryResolveVectors : List Vector :=
  [directoryResolve "directory-resolve.unregistered" 0 0,
   directoryResolve "directory-resolve.unregistered-full-rights" 0 15] ++
  (List.range 16).map (fun held =>
    directoryResolve s!"directory-resolve.held-{held}" 1 held.toUInt64) ++
  [directoryResolve "directory-resolve.held-out-of-range" 1 16,
   directoryResolve "directory-resolve.maximum-words" 0xffffffffffffffff
     0xffffffffffffffff]

/-- Fault-handler routes (#488): the bound `#DE` delivery from A to C, the
default for another class, a page fault, a busy handler, a fault from B and
one from the handler C itself, the bound handler's terminate, and the refused
replies (wrong subject, nothing suspended, another decision, unknown event). -/
def faultHandlerVectors : List Vector := [
  faultHandlerRoute "fault-handler.deliver" 0 0 1 1,
  faultHandlerRoute "fault-handler.other-class" 0 3 1 1,
  faultHandlerRoute "fault-handler.page-fault" 0 14 1 1,
  faultHandlerRoute "fault-handler.handler-busy" 0 0 1 0,
  faultHandlerRoute "fault-handler.other-subject" 0 0 2 1,
  faultHandlerRoute "fault-handler.handler-faults" 0 0 3 1,
  faultHandlerRoute "fault-handler.reply-terminate" 1 1 3 1,
  faultHandlerRoute "fault-handler.reply-wrong-subject" 1 1 2 1,
  faultHandlerRoute "fault-handler.reply-nothing-suspended" 1 0 3 1,
  faultHandlerRoute "fault-handler.reply-other-decision" 1 1 3 2,
  faultHandlerRoute "fault-handler.unknown-event" 2 0 1 1]

/-- Keyboard-echo device authority (#493): every subject code 0--4 against the
assigned device 0 and another device 1, then the holder against the maximum
device word and the maximum words. -/
def deviceAuthorizeVectors : List Vector :=
  ((List.range 5).flatMap fun subject => (List.range 2).map fun device =>
    deviceAuthorize s!"device-authorize.subject-{subject}-device-{device}"
      subject.toUInt64 device.toUInt64) ++
  [deviceAuthorize "device-authorize.holder-maximum-device" 1 0xffffffffffffffff,
   deviceAuthorize "device-authorize.maximum-words" 0xffffffffffffffff 0xffffffffffffffff]

/-- Timer-server kernel decisions (#487): C's arm at and around the bound,
arms from A and B, sends to the server from each subject, the expiry with and
without an armed alarm, C's wake of A and refused wakes, and an unknown
event. -/
def timerServerVectors : List Vector := [
  timerServerDecide "timer-server.arm-holder-max" 0 3 65535,
  timerServerDecide "timer-server.arm-holder-min" 0 3 1,
  timerServerDecide "timer-server.arm-holder-zero" 0 3 0,
  timerServerDecide "timer-server.arm-holder-over" 0 3 65536,
  timerServerDecide "timer-server.arm-holder-maximum-word" 0 3 0xffffffffffffffff,
  timerServerDecide "timer-server.arm-client" 0 1 1000,
  timerServerDecide "timer-server.arm-other" 0 2 1000,
  timerServerDecide "timer-server.send-client" 1 1 0,
  timerServerDecide "timer-server.send-other" 1 2 0,
  timerServerDecide "timer-server.send-server" 1 3 0,
  timerServerDecide "timer-server.expire-armed" 2 0 1,
  timerServerDecide "timer-server.expire-idle" 2 0 0,
  timerServerDecide "timer-server.wake-holder" 3 3 1,
  timerServerDecide "timer-server.wake-other-signaller" 3 2 1,
  timerServerDecide "timer-server.wake-other-client" 3 3 2,
  timerServerDecide "timer-server.unknown-event" 4 3 1]
/-- Frame-server decision checks (#486): the image's four decisions (grant
to A, A's over-budget refusal, A's revocation, the republished grant to B),
then every rejection of a hostile decision (outside the pool, frame in use,
amplified or empty rights, over budget, untruthful refusals, reclaim of a
frame the client does not hold), an accepted reclaim and pool-exhausted
refusal, an unknown op, and maximum words. -/
def frameServerVectors : List Vector := [
  frameServerCheck "frame-server.grant-a" 1 1 0 1 3 3,
  frameServerCheck "frame-server.refuse-a-over-budget" 2 0 1 1 0 3,
  frameServerCheck "frame-server.revoke-a" 5 0 1 1 0 3,
  frameServerCheck "frame-server.grant-b-republished" 1 1 0 2 3 3,
  frameServerCheck "frame-server.grant-outside-pool" 1 0 0 1 3 3,
  frameServerCheck "frame-server.grant-frame-in-use" 1 3 0 1 3 3,
  frameServerCheck "frame-server.grant-amplified-rights" 1 1 0 1 4 3,
  frameServerCheck "frame-server.grant-empty-rights" 1 1 0 1 0 3,
  frameServerCheck "frame-server.grant-over-budget" 1 1 1 1 3 3,
  frameServerCheck "frame-server.refuse-within-budget" 2 0 0 1 0 3,
  frameServerCheck "frame-server.refuse-pool-with-free-frame" 3 1 0 1 0 3,
  frameServerCheck "frame-server.refuse-pool-exhausted" 3 0 0 1 0 3,
  frameServerCheck "frame-server.reclaim-held" 4 2 1 1 0 3,
  frameServerCheck "frame-server.reclaim-not-holder" 4 3 0 1 0 3,
  frameServerCheck "frame-server.unknown-op" 0 1 0 1 3 3,
  frameServerCheck "frame-server.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff]

/-- Frame-server view words (#486): a free pool frame for A and for B, a frame
outside the pool, a frame held by another client, a frame held by the
client, the pool-exhausted bit, ops without a frame, and maximum words. -/
def frameServerViewVectors : List Vector := [
  frameServerView "frame-server-view.free-for-a" 1 0 2 0 1 2,
  frameServerView "frame-server-view.free-for-b" 1 0 2 0 2 1,
  frameServerView "frame-server-view.outside-pool" 1 2 2 0 1 2,
  frameServerView "frame-server-view.held-by-other" 1 1 2 2 1 1,
  frameServerView "frame-server-view.held-by-client" 4 0 2 1 1 1,
  frameServerView "frame-server-view.pool-exhausted" 3 0 2 0 1 0,
  frameServerView "frame-server-view.refuse-budget" 2 0 2 1 1 1,
  frameServerView "frame-server-view.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff]

/-- On every user-copy vector, the generated adapter's Lean definition gives
the model's answer. -/
theorem user_copy_policy_vectors_agree :
    userCopyPolicyVectors.all (fun v => match v.words with
      | [flags, start, length, text, stack, top] =>
        UserCopyPolicy.copyPolicy flags start length text stack top == v.expected
      | _ => false) = true := by
  decide

end LeanOS.Oracle
