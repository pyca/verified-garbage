module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Step
public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The public block counter terminates, including the empty message. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem nonzero_count {s : State} {n : Nat} (hn : n < 2^64) (hc : s.gpr .x3=BitVec.ofNat 64 n) :
    isa.eval (.nonzero .x .x3) s=some (!decide (n=0)) := by
  change some (s.read .x .x3 != 0)=_
  simp only [State.read,BitVec.setWidth_eq,hc,ofNat_ne_zero hn]

theorem loop_ok {s₀ s : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) (h : Inv s₀ k s) :
    WP isa (.loop (Impl.AesCbc.AArch64.Encrypt.step (R s₀)) (.nonzero .x .x3)) s (Inv s₀ (N s₀)) := by
  let I := fun j t => ∃ k,k+j=N s₀ ∧ k<N s₀ ∧ Inv s₀ k t
  refine WP.loop (M:=isa) I (fun j t ⟨k,hkj,hk,hi⟩ => ?_) (N s₀-k) s ⟨k,by omega,hk,h⟩
  refine WP.mono (step_ok hp hk hi) fun u hu => ?_
  have he := nonzero_count (by have := hp.data_wrap; omega) hu.count
  by_cases hend : k+1=N s₀
  · refine Or.inl ⟨?_,?_⟩
    · rw [he,hend,Nat.sub_self]; rfl
    · rw [hend] at hu; exact hu
  · refine Or.inr ⟨?_,N s₀-(k+1),by omega,k+1,?_⟩
    · rw [he,decide_eq_false (by omega)]; rfl
    · exact ⟨by omega,by omega,hu⟩

def middle (nr : Nat) : Prog isa :=
  .ite (.zero .x .x3) (.block [])
    (.seq (.block (Impl.AesCbc.AArch64.Encrypt.enter nr))
      (.loop (Impl.AesCbc.AArch64.Encrypt.step nr) (.nonzero .x .x3)))

theorem middle_ok {s₀ s : State} (hp : UPre s₀) (he : Env s₀ s)
    (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4)
    (hch : s.v .v31 ^^^ s.v .v30=chain s₀ 0) (hm : s.mem=s₀.mem) :
    WP isa (middle (R s₀)) s (Inv s₀ (N s₀)) := by
  have hev := zero_count (n:=N s₀) (by exact (s₀.gpr .x4).isLt) (h3.trans (x4_ofNat s₀))
  by_cases hn : N s₀=0
  · refine WP.ite true (by rw [hev,hn]; rfl) (fun _ => WP.block_nil ?_) (fun hf => by cases hf)
    rw [hn]
    refine ⟨by omega,he,?_,?_,hch,?_,fun hc => by omega⟩
    · simpa only [blk,Nat.mul_zero,BitVec.add_zero,hn] using h2
    · rw [h3,x4_ofNat,hn]
    · intro i hi; rw [hm]; rfl
  · refine WP.ite false (by rw [hev,decide_eq_false hn]) (fun hf => by cases hf) (fun _ => ?_)
    exact WP.seq (WP.mono (entry_ok hp (by omega) he h2 h3 hch hm)
      fun t ht => loop_ok hp (by omega) ht)
end VG.Proof.AesCbc.AArch64.Encrypt
