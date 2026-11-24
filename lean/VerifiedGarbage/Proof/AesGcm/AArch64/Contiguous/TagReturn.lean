module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagBytes
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Finish
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.AesGcm.AArch64 (alenO restore)
open VG.Impl.Gcm.AArch64.Pmull (Y)
open VG.Spec.Gcm (Block toBytes ofBytes blockAt)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.AArch64.Stitch (sch kp)
open VG.Impl.AesGcm.AArch64.Contiguous.Tag (finish)

theorem return_ok {wn R n al : Nat} {Ctx St W Tg : Addr} {s o : State} {H y : Block}
    (law : MulKey) (env : Env wn Ctx St W o.sp s) (hk : Fast.HKey H s) (hy : s.v Y = ext8 y y)
    (rounds : R = 10 ∨ R = 12 ∨ R = 14) (r22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (length : s.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2^64)
    (aad : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al) (ha : al < 2^64)
    (save : SavedAt s.mem W o) (tag : Covers [⟨Tg,16⟩] s.wr) (dest : s.gpr .x28 = Tg)
    (dis : (⟨Tg,16⟩ : Region).Disjoint (workR wn W)) :
    let z := Spec.Gcm.mul (y ^^^ ofBytes (Proof.Gcm.lensBlock al n)) H
    WP isa (.seq (Impl.Gcm.AArch64.Stitch.byRounds finish) (.block restore)) s fun t =>
      bytesAt t.mem Tg 16 = toBytes (z ^^^ ciphOf s.mem Ctx R (blockAt s.mem St)) ∧
      GprAbi o t ∧ Frame [⟨Tg,16⟩] s.mem t.mem := by
  dsimp only
  refine WP.seq (Stitch.byRoundsG_ok rounds r22 ?_)
  intro a regs mem vec sp rd wr
  have keep (r : Reg) (h : r ∈ [Reg.x19,.x20,.x21]) : a.gpr r = s.gpr r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> exact regs _ (by decide) (by decide)
  have e := env.keep keep sp rd wr
  have a28 := (regs .x28 (by decide) (by decide)).trans dest
  have a26 := (regs .x26 (by decide) (by decide)).trans length
  have aKey := hk.of_v (congrFun vec _) (congrFun vec _) (congrFun vec _)
  have aY := (congrFun vec Y).trans hy
  refine (finish_ok rounds law aKey aY ?_ ?_ ?_ ?_).mono ?_
  · intro i hi
    rw [e.x21]
    exact e.perm.ctxR (by omega_using [hi,rounds])
  · rw [e.x20]; exact e.perm.stR (by decide)
  · rw [e.x19]; exact e.perm.wR (by decide)
  · rw [wr,a28,BitVec.add_zero]
    exact tag _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩
  intro b ⟨mask, cipher, store, gpr, bsp, brd, bwr⟩
  have written : Frame [⟨Tg,16⟩] s.mem b.mem := by
    rw [store,a28,mem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved := save.frame written (by
    intro r hr; have eq := List.mem_singleton.mp hr; subst r
    exact (dis.sub_right (Lay.wSub (by have := env.perm.hWn; omega))).symm)
  have bs := bsp.trans e.sp
  have access : Covers [⟨W,wn⟩] (b.rd++b.wr) := by rw [brd,bwr]; exact covers_left e.perm.w
  refine (exit_ok ((gpr _ (by decide) (by decide)).trans e.x19) bs access saved
    (by have := env.perm.hWn; omega)).mono ?_
  intro t ⟨abi,mt,_,_,_⟩
  rw [mt]
  refine ⟨?_,abi,written⟩
  rw [store,a28]
  rw [tagBytes _ _ _ _ _ _ _ cipher]
  simp only [aadLength,e.x19,e.x20,sch,kp,e.x21,a26,mem,aad,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hn]

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
