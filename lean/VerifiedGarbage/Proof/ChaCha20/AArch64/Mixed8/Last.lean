module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Store
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Neon4 (DataTo)

structure Same (s u : State) : Prop where
  gpr : u.gpr = s.gpr
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp

theorem Same.trans {s a u : State} (h : Same s a) (h' : Same a u) : Same s u :=
  ⟨h'.gpr.trans h.gpr,h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp⟩

theorem xorScalarRowFrom_ok (s : State) (r : Reg) (k : Fin 8)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16)
    (hsrc : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (384 + 16 * k.val)) 16)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16) :
    WP isa (.block (xorScalarRowFrom r k)) s fun u =>
      u.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16
        (s.mem.read (s.gpr r + BitVec.ofNat 64 (384 + 16 * k.val)) 16 ^^^
          s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16) ∧ Same s u := by
  have ha : (16 * k.val) % 16 = 0 ∧ 16 * k.val < 4096 * 16 := by omega
  have hb : (384 + 16 * k.val) % 16 = 0 ∧ 384 + 16 * k.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorScalarRowFrom,runBlock_cons,runBlock_nil,exec,addr,
    ha,hb,and_self,ite_true,State.load,hin,hsrc,State.setV,reduceVOpEval,State.store,hout,
    Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- `xorScalarRow` writes only the destination's last 128 bytes. -/
theorem data_frame128 {m₀ m : Mem} {q p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p 128 out done) : Frame [⟨p,128⟩] m₀ m := h.frame

/-- The integer blocks' keystream (at `b`) XORed with the source's last 128
bytes (at `q`, from `r`) into the destination's (at `p`, from `x1`). -/
theorem xorScalarListFrom_ok (r : Reg) (ks : List (Fin 8)) (hn : ks.Nodup)
    {m₀ : Mem} {q p b : Addr} {done : List Nat} {s : State}
    (h : DataTo m₀ s.mem q p 128 (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16) done)
    (hq : s.gpr r + BitVec.ofNat 64 384 = q) (hp : s.gpr .x1 + BitVec.ofNat 64 384 = p)
    (hbp : s.gpr .x3 = b)
    (hdis : (⟨b,128⟩ : Region).Disjoint ⟨p,128⟩)
    (halias : q = p ∨ (⟨q,128⟩ : Region).Disjoint ⟨p,128⟩)
    (hf : ∀ k ∈ ks, k.val ∉ done)
    (hin : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16)
    (hsrc : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (384 + 16 * k.val)) 16)
    (hout : ∀ k : Fin 8, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16) :
    WP isa (.block (ks.flatMap (xorScalarRowFrom r))) s fun u =>
      DataTo m₀ u.mem q p 128 (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16)
        (ks.map Fin.val ++ done) ∧ Same s u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h,⟨rfl,rfl,rfl,rfl⟩⟩
  | cons k ks ih =>
    apply WP.block_append
    refine (xorScalarRowFrom_ok s r k (hin k) (hsrc k) (hout k)).mono fun a ⟨hm,hs⟩ => ?_
    have he : s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val) =
        p + BitVec.ofNat 64 (16 * k.val) := by rw [BitVec.ofNat_add,← BitVec.add_assoc,hp]
    have hes : s.gpr r + BitVec.ofNat 64 (384 + 16 * k.val) =
        q + BitVec.ofNat 64 (16 * k.val) := by rw [BitVec.ofNat_add,← BitVec.add_assoc,hq]
    have hr : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16 =
        m₀.read (b + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hbp]
      exact (data_frame128 h).read (r := ⟨b,128⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hdis) (by decide)
    have ha : DataTo m₀ a.mem q p 128 (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16)
        (k.val :: done) := by
      rw [hm,he,hes,hr]
      exact h.store (by omega) (by decide)
        (h.src halias (by omega) (by decide) (hf k (List.mem_cons_self ..)))
    have hf' : ∀ l ∈ ks, l.val ∉ k.val :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 ((Fin.ext he) ▸ hl),
        hf l (List.mem_cons_of_mem _ hl)⟩
    have hin' : ∀ l : Fin 8, InRegions (a.rd ++ a.wr) (a.gpr .x3 + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l; rw [hs.rd,hs.wr,hs.gpr]; exact hin l
    have hsrc' : ∀ l : Fin 8, InRegions (a.rd ++ a.wr) (a.gpr r + BitVec.ofNat 64 (384 + 16 * l.val)) 16 := by
      intro l; rw [hs.rd,hs.wr,hs.gpr]; exact hsrc l
    have hout' : ∀ l : Fin 8, InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (384 + 16 * l.val)) 16 := by
      intro l; rw [hs.wr,hs.gpr]; exact hout l
    refine (ih (List.nodup_cons.mp hn).2 ha (by rw [hs.gpr]; exact hq) (by rw [hs.gpr]; exact hp)
      (by rw [hs.gpr]; exact hbp) hf' hin' hsrc' hout').mono fun u ⟨hu,hsu⟩ => ⟨?_,hs.trans hsu⟩
    intro x
    simpa only [DataTo,List.map_cons,List.cons_append,
      List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu x

end VG.Proof.ChaCha20.AArch64.Mixed8
