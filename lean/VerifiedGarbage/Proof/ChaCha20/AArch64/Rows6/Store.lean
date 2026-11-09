module
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
public import VerifiedGarbage.Proof.Framework.Semantics

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Store
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Ops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Neon4 (DataTo)

structure StoreSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : ∀ k : Fin 24, s'.v (vreg k) = s.v (vreg k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreSame.trans {s₀ s₁ s₂ : State} (h : StoreSame s₀ s₁) (h' : StoreSame s₁ s₂) :
    StoreSame s₀ s₂ := ⟨h'.gpr.trans h.gpr, fun k => (h'.v k).trans (h.v k),
      h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

/-- Row `k`: the source's (at `r`) XORed with the keystream's into the
destination (at `x1`). -/
theorem xorRowFrom_ok (s : State) (r : Reg) (k : Fin 24)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block (xorRowFrom r k)) s fun u =>
      u.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16
        (s.mem.read (s.gpr r + BitVec.ofNat 64 (16 * k.val)) 16 ^^^ s.v (vreg k)) ∧ StoreSame s u := by
  have ha : 16 * k.val % 16 = 0 ∧ 16 * k.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [xorRowFrom,runBlock_cons,runBlock_nil,exec,addr,ha,and_self,ite_true,State.load,hin,
    Option.bind_some,Option.map_some,isa,runStep_some,RegUpd.gpr_setV,RegUpd.v_setV,
    vreg_ne,ite_false,VOp.eval,State.store,RegUpd.wr_setV,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl⟩
  intro l
  simp only [RegUpd.v_setV,vreg_ne,ite_false]

/-- The rows `ks`, from the source at `r` (`q`) to the destination at `x1`
(`p`), which is the source or apart from it in their first 384 bytes. -/
theorem xorListFrom_ok (r : Reg) (ks : List (Fin 24)) (hn : ks.Nodup)
    {m₀ : Mem} {q p : Addr} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : DataTo m₀ s.mem q p 384 out done) (hq : s.gpr r = q) (hp : s.gpr .x1 = p)
    (halias : q = p ∨ (⟨q, 384⟩ : Region).Disjoint ⟨p, 384⟩)
    (hv : ∀ k : Fin 24, s.v (vreg k) = out k.val)
    (hfresh : ∀ k ∈ ks, k.val ∉ done)
    (hin : ∀ k ∈ ks, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : ∀ k ∈ ks, InRegions s.wr (p + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block (ks.flatMap (xorRowFrom r))) s fun u =>
      DataTo m₀ u.mem q p 384 out (ks.map Fin.val ++ done) ∧ StoreSame s u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨hd,rfl,fun _ => rfl,rfl,rfl,rfl⟩
  | cons k ks ih =>
    have hi : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hq]; exact hin k (List.mem_cons_self ..)
    have ho : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hp]; exact hout k (List.mem_cons_self ..)
    apply WP.block_append
    refine (xorRowFrom_ok s r k hi ho).mono fun a ⟨hm,hs⟩ => ?_
    have hd' : DataTo m₀ a.mem q p 384 out (k.val :: done) := by
      rw [hm,hp,hq,hv k]
      exact hd.store (by omega) (by decide)
        (hd.src halias (by omega) (by decide) (hfresh k (List.mem_cons_self ..)))
    have hq' : a.gpr r = q := by rw [hs.gpr,hq]
    have hp' : a.gpr .x1 = p := by rw [hs.gpr,hp]
    have hv' : ∀ l : Fin 24, a.v (vreg l) = out l.val := by intro l; rw [hs.v,hv]
    have hf' : ∀ l ∈ ks, l.val ∉ k.val :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 ((Fin.ext e) ▸ hl),
        hfresh l (List.mem_cons_of_mem _ hl)⟩
    have hi' : ∀ l ∈ ks, InRegions (a.rd ++ a.wr) (q + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l hl; rw [hs.rd,hs.wr]; exact hin l (List.mem_cons_of_mem _ hl)
    have ho' : ∀ l ∈ ks, InRegions a.wr (p + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l hl; rw [hs.wr]; exact hout l (List.mem_cons_of_mem _ hl)
    refine (ih (List.nodup_cons.mp hn).2 hd' hq' hp' hv' hf' hi' ho').mono fun u ⟨hu,hau⟩ =>
      ⟨?_,hs.trans hau⟩
    intro x
    simpa only [DataTo,List.map_cons,List.cons_append,List.mem_append,List.mem_cons,or_assoc,
      or_left_comm] using hu x
end VG.Proof.ChaCha20.AArch64.Rows6
