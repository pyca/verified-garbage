module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.WordsCanonical

/-! Both comb helpers share the existing DSA register-save and restore boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.X86.Spill VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def scratch (prepare : Bool) (n : Nat) : List (Nat × Nat) :=
  VG.Impl.Dsa.X86.Pow.scratch n ++ if prepare then [(context n,272*n)] else []

theorem core_ranges_scratch {n e : Nat} (h : Supported n e) (prepare : Bool) :
    ∀ r ∈ coreRanges prepare n e, ∃ w ∈ scratch prepare n, w.1≤r.1 ∧ r.1+r.2≤w.1+w.2 := by
  cases prepare <;>
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem core_saved {n e : Nat} {base : Addr} {s t : State} {g : Reg → BitVec 32}
    (h : Supported n e) (prepare : Bool) (O : Outs base (coreRanges prepare n e) s.mem t.mem)
    (H : Saved s.mem (off base) g VG.Impl.Dsa.X86.Pow.slots) :
    Saved t.mem (off base) g VG.Impl.Dsa.X86.Pow.slots := by
  intro p hp
  have hp' : 8≤p.2 ∧ p.2+4≤24 := by
    simp only [VG.Impl.Dsa.X86.Pow.slots,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> decide
  have apart : ∀ r ∈ coreRanges prepare n e, r.1+r.2≤8 ∨ 24≤r.1 := by
    cases prepare <;>
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  rw [show t.mem.readW (off base p.2) 32=s.mem.readW (off base p.2) 32 from
    Mem.readW_congr (fun i hi => O _ (by
      intro r hr
      rw [ofs_off base (by omega)]
      have := apart r hr
      omega))]
  exact H p hp

theorem body_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (prepare : Bool) (E : Pow.Entry s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : prepare=false → canonical n e m (wordsVal s.mem base (slot n 5) n) base s.mem) :
    WP isa (body prepare n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      (prepare=true → canonical n e m (wordsVal s.mem base (slot n 5) n) base t.mem) ∧
      Outs base (scratch prepare n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have hz24 : 24≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold body
  refine WP.seq (WP.mono (Pow.save_ok E hz24) fun u ⟨Su,Saved,Ou,Ku⟩ => ?_)
  have vals : ∀ {d k : Nat}, 24≤d → d+4*k≤2^64 → val32 u.mem base d k=val32 s.mem base d k :=
    fun hd hk => Ou.val32 (by omega) hk
  have bounds : 24≤slot n 0 ∧ slot n 0+8*n≤2^64 ∧ 24≤slot n 5 ∧ slot n 5+8*n≤2^64 ∧
      24≤slot n 8 ∧ slot n 8+4*e≤2^64 ∧ 24≤context n ∧
      context n+8*Proof.Dsa.FixedBaseComb.contextWords (layout n e)≤2^64 := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have V : wordsVal u.mem base (slot n 0) n=m := by
    rw [wordsVal_eq_val32,vals bounds.1 (by have := bounds.2.1; omega),←wordsVal_eq_val32,hv]
  have G : wordsVal u.mem base (slot n 5) n=wordsVal s.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32,wordsVal_eq_val32]
    exact vals bounds.2.2.1 (by have := bounds.2.2.2.1; omega)
  have X : val32 u.mem base (slot n 8) e=val32 s.mem base (slot n 8) e :=
    vals bounds.2.2.2.2.1 bounds.2.2.2.2.2.1
  have Hu : prepare=false → canonical n e m (wordsVal u.mem base (slot n 5) n) base u.mem := by
    intro hp
    unfold canonical
    rw [wordsAt_canonical,Ou.wordsVal (.inr bounds.2.2.2.2.2.2.1) bounds.2.2.2.2.2.2.2,←wordsAt_canonical,G]
    exact H hp
  refine WP.seq (WP.mono (core_ok h prepare Su V hm odd Hu) fun v ⟨Vv,Cv,Ov,Kv⟩ => ?_)
  refine WP.mono (Pow.restore_ok (Su.of_keeps Kv (by decide)) hz24 (core_saved h prepare Ov Saved))
    fun t R => ⟨by rw [R.mem,Vv,G,X],?_,?_,R.abi (by decide) (by decide) ?_,?_,?_⟩
  · intro hp
    unfold canonical
    rw [R.mem]
    simpa only [canonical,G] using Cv hp
  · rw [R.mem]
    have saveFrame : Outs base (scratch prepare n) s.mem u.mem :=
      Outs.of_outside (Ou.mono (o' := 0) (n' := 64) (by decide) (by decide)) (by simp [scratch,VG.Impl.Dsa.X86.Pow.scratch])
    exact saveFrame.trans (VG.Proof.Mont.X86.Comb.widen Ov (core_ranges_scratch h prepare))
  · exact (Kv.1 _ (by decide)).trans (Ku.1 _ (by decide))
  · rw [R.rd,Kv.2.1,Ku.2.1]
  · rw [R.wr,Kv.2.2,Ku.2.2]

end VG.Proof.Dsa.X86.Comb
