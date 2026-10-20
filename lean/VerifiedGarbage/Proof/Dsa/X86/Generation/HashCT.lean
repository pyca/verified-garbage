module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.HashArguments
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTCalls
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTCalls

/-! # Seed hashing inherits the timing guarantees of every streaming-hash variant -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation

theorem hashHead_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashAt K len)) (.block hashHead) (Two (HashBaseAt K len)) := by
  refine two_piece [] (by intro _ _ _ _ _ r hr; cases hr) (by taint_decide) ?_
  intro p s R
  refine WP.mono hashHead_ok fun t ⟨bx, _, Kt⟩ => ?_
  exact ⟨R.keep Kt (by decide) (by decide) (by decide) (by decide), by rw [bx, R.ebp]⟩

theorem hashUpdateArgs_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashBaseAt K len)) (.block (hashUpdateArgs len)) (Two (HashUpdateAt K len)) := by
  refine two_piece [] (by intro _ _ _ _ _ r hr; cases hr) (hc := .block []) (by rfl) ?_
  intro p s R
  refine WP.mono (hashUpdateArgs_ok len) fun t ⟨dx, cx, ax, _, Kt⟩ => ?_
  exact ⟨⟨R.1.keep Kt (by decide) (by decide) (by decide) (by decide), (Kt.1 _ (by decide)).trans R.2⟩,
    ax, cx, dx.trans R.1.esi⟩

theorem hashFinalizeArgs_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashBaseAt K len)) (.block (hashFinalizeArgs len)) (Two (HashFinalAt K len)) := by
  refine two_piece [] (by intro _ _ _ _ _ r hr; cases hr) (hc := .block []) (by rfl) ?_
  intro p s R
  refine WP.mono (hashFinalizeArgs_ok len) fun t ⟨dx, ax, cx, _, Kt⟩ => ?_
  exact ⟨⟨R.1.keep Kt (by decide) (by decide) (by decide) (by decide), (Kt.1 _ (by decide)).trans R.2⟩,
    ax, cx, dx.trans R.1.edi⟩

theorem seedHash_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashAt K len)) (seedHash H len) (fun _ _ => True) := by
  unfold seedHash
  exact RelCT.seq (hashHead_ct K len) (RelCT.seq (hashInit_ct K len)
    (RelCT.seq (hashUpdateArgs_ct K len) (RelCT.seq (hashUpdate_ct K len)
      (RelCT.seq (hashFinalizeArgs_ct K len) (hashFinal_ct K len)))))
end VG.Proof.Dsa.X86.Generation
