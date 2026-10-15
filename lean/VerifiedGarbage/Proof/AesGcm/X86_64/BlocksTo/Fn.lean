module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Full
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Tail
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask

/-!
# AES-GCM on whole blocks out of place, x86-64: correctness

Untrusted: everything here is checked by Lean. The entry, the first
`16 ⌊n / 16⌋` blocks in one pass (with out-of-place interleaved loops, if
any), and the rest, copied and encrypted in place by a call (`encrypt_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode StitchToOkM)

theorem encrypt_wpB {M : CtxMode} (B : BlkFn M) (aligned full : Bool) (st : Option (Prog isa))
    (hst : ∀ p, st = some p → StitchToOkM M p (if full then 1 else 16)) {s : State}
    (hp : BT M s) :
    WP isa (encrypt B.enc st aligned full) s (Done s) := by
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ => ?_)
  cases st with
  | none =>
    exact WP.seq (WP.block_nil (tail_ok hp B (mid_entry hp (hg _ (by decide) (by decide))
      (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      hk hf hrd hwr)))
  | some p =>
    cases full with
    | false =>
      exact WP.seq (WP.seq (WP.mono (stitch_ok hp (hst p rfl) h11 h10 hg hk hf hrd hwr) fun st M =>
        WP.mono (rest_ok hp rfl M) fun st' M' => tail_ok hp B M'))
    | true =>
      exact WP.seq (WP.seq (WP.mono (stitchFullTo_ok hp (hst p rfl) h11 h10 hg hk hf hrd hwr) fun st M =>
        WP.mono (restFullTo_ok hp M) fun st' M' => tail_ok hp B M'))

theorem encrypt_wp {M : CtxMode} (B : BlkFn M) (aligned full : Bool) (st : Option (Prog isa))
    (hst : ∀ p, st = some p → StitchToOkM M p (if full then 1 else 16)) {s : State}
    (hpre : Proof.AesGcm.blocksToPreM M s) :
    WP isa (encrypt B.enc st aligned full) s (Done s) :=
  encrypt_wpB B aligned full st hst (BT.ofM hpre)

end VG.Proof.AesGcm.X86_64.BlocksTo
