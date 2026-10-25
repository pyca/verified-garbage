module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Table
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Copy
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.TableLayout

/-! Public lookup of a nonzero digit pair, with all pointer bounds checked. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem fetchHead_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d) :
    WP isa (.block fetchHead) s fun t =>
      t.gpr .x16 = off base (tablePt d).x ∧ Keeps [.x2,.x16,.x17] s t := by
  have hsub : BitVec.ofNat 64 d - 1 = BitVec.ofNat 64 (d-1) := by
    apply BitVec.eq_of_toNat_eq
    change (2^64-1+d%(2^64))%(2^64)=(d-1)%(2^64)
    omega
  apply WP.of_runBlock
  simp only [fetchHead,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat) < 4096 by decide,show 16*0 < Size.x.bits by decide,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,h2,hs.x0,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    show (144 : BitVec 16).setWidth 64 = BitVec.ofNat 64 144 from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change base+BitVec.ofNat 64 5280+(BitVec.ofNat 64 d-1)*BitVec.ofNat 64 144 = off base (tablePt d).x
    rw [hsub,←BitVec.ofNat_mul]
    change base+BitVec.ofNat 64 5280+BitVec.ofNat 64 ((d-1)*144)=
      base+BitVec.ofNat 64 (5280+144*(d-1))
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact congrArg (base+·) (congrArg (BitVec.ofNat 64) (by omega))
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem fetch_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    WP isa (.block fetch) s fun t =>
      Changes base entryWork s t ∧ PointAt base t entry P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have ex_bound : entry.x+48 ≤ 8192 := by decide
  have ey_bound : entry.y+48 ≤ 8192 := by decide
  have htab := table_coord_bounds h1 h15
  have ha : (tablePt d).x+144 ≤ 8192 := by
    have hb := (htab (tablePt d).z (by simp)).2.1
    change _+48 ≤ 7440 at hb
    dsimp only [tablePt] at hb ⊢; omega
  have hab : (tablePt d).x ≤ 8192 := by omega
  have hsep : ∀ e ∈ coordinates entry,e+48 ≤ (tablePt d).x := by
    have hh : ∀ e ∈ coordinates entry,e+48 ≤ tableAt := by decide
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  have sepX := hsep entry.x (by decide)
  have sepY := hsep entry.y (by decide)
  have sepZ := hsep entry.z (by decide)
  rw [fetch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 6 hs₁ p₁ (a:=(tablePt d).x) (src:=0) (dst:=entry.x)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by simpa using hsep _ (by simp))))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 6 hs₂ p₂ (a:=(tablePt d).x) (src:=48) (dst:=entry.y)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 6 hs₃ p₃ (a:=(tablePt d).x) (src:=96) (dst:=entry.z)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have e_x : num base t entry.x = num base s (tablePt d).x := by
    change wordsVal t.mem base entry.x 6 = wordsVal s.mem base (tablePt d).x 6
    rw [u₄.wordsVal (by decide) (by omega),
      u₃.wordsVal (by decide) (by omega),x,k₁.mem]
    rfl
  have e_y : num base t entry.y = num base s (tablePt d).y := by
    change wordsVal t.mem base entry.y 6 = wordsVal s.mem base (tablePt d).y 6
    rw [u₄.wordsVal (by decide) (by omega),y]
    rw [u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  have e_z : num base t entry.z = num base s (tablePt d).z := by
    change wordsVal t.mem base entry.z 6 = wordsVal s.mem base (tablePt d).z 6
    rw [z,u₃.wordsVal (Or.inr (by omega)) (by omega),
      u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  have kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  have u : Unch base entryWork s.mem t.mem := by
    rw [←k₁.mem]
    exact (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> decide)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_x
    have ey := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_y
    have ez := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_z
    change val base t entry.x = val base s (tablePt d).x at ex
    change val base t entry.y = val base s (tablePt d).y at ey
    change val base t entry.z = val base s (tablePt d).z at ez
    rw [ex,ey,ez]; exact hp.2
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
