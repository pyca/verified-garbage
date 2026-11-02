module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkFront
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The checks of an RSA key on RISC-V: a function, from its parts

`fn_ok`: `KeyCheck.fn` from the precondition (`KPre`): `save`, the moves of
the arguments (whatever they establish, `MV`), the entry's checks of `e` and
`n` (`tail_ok`), then the valid branch (given), or 0 returned, and the
registers restored. `ldSp_ok`: a stack argument loaded through `t0 = sp`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved save restore)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Bignum.RISCV64.Pub (sat)

theorem stackArgAddr_eq (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  unfold stackArgAddr
  rw [Nat.mul_zero]
  exact (congrArg (· + BitVec.ofNat 64 (8 * i)) (add_ofNat_zero' s.sp)).symm

/-- The stack argument `i` is readable. -/
theorem KPre.arg_rd {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) {i : Nat}
    (hi : i < na) : InRegions (s0.rd ++ s0.wr) (stackArgAddr s0 i) 8 := by
  have hs := h.sp
  refine ⟨_, List.mem_append_left _ h.args, ?_⟩
  rw [stackArgAddr_eq s0 i]
  exact Offset.contains_base (d := 8 * i) (n := 8) (k := 8 * na) (stackArgAddr s0 0) (by omega) (by omega)

theorem KPre.arg_al {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) {i : Nat}
    (hi : i < na) : (stackArgAddr s0 i).toNat % 8 = 0 := by
  have hs := h.sp
  have h16 := h.sp16
  have e : (stackArgAddr s0 i).toNat = s0.sp.toNat + 8 * i := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

/-- A stack argument loaded through `t0 = sp`. -/
theorem ldSp_ok {u : State} (h0 : u.gpr .t0 = u.sp) {r : Reg} {i o : Nat} (ho : o = 8 * i) (hi : 8 * i < 2048)
    (hin : InRegions (u.rd ++ u.wr) (stackArgAddr u i) 8) (hal : (stackArgAddr u i).toNat % 8 = 0)
    {rest : List Instr} {Q : State → Prop} (k : WP isa (.block rest) (u.write r (stackArg u i)) Q) :
    WP isa (.block (.load .d r .t0 o :: rest)) u Q := by
  subst ho
  have e : u.gpr .t0 + BitVec.ofNat 64 (8 * i) = stackArgAddr u i := by rw [h0]; rfl
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d hi (by rw [e]; exact hal) (by rw [e]; exact hin), ?_⟩
  rw [e]
  exact k

/-- `save`'s state, as `KBase`. -/
theorem KBase.of_saved {s0 u : State} {B : Addr} {Z : Nat} (h : Saved s0 B u) (hZ : 96 ≤ Z) :
    KBase B Z s0 u :=
  ⟨h.keep.2.1, h.keep.2.2, fun x hx => h.out x (Or.inr (by omega)), h.saved, h.s11⟩

/-- The registers the code may change, but `ra`. -/
abbrev fnRegs : List Reg := [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7,
  .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .t3, .t4, .t5, .t6]

theorem fn_ok {s0 : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (hoS : 8 * oS < 2048)
    {moves : List Instr} {loads body : List (Prog isa)} {E N : Addr} {L : Nat} {ok : Bool}
    {MV : State → Prop}
    (hm : ∀ u, Saved s0 B u → WP isa (.block moves) u fun v => MV v ∧ v.mem = u.mem ∧ v.rd = u.rd ∧
      v.wr = u.wr ∧ v.gpr .s11 = u.gpr .s11 ∧ v.gpr .a4 = off E 0 ∧ v.gpr .a5 = BitVec.ofNat 64 L ∧
      v.gpr .s1 = off N 0 ∧ v.gpr .s2 = BitVec.ofNat 64 K)
    (hL : 1 ≤ L) (hL' : L ≤ 1024) (hE : (⟨E, L⟩ : Region) ∈ s0.rd) (dE : (⟨E, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (wE : E.toNat + L ≤ 2 ^ 64) (hN : (⟨N, K⟩ : Region) ∈ s0.rd) (dN : (⟨N, K⟩ : Region).Disjoint ⟨B, Z⟩)
    (wN : N.toNat + K ≤ 2 ^ 64)
    (hok : ok = true → Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem E L)) = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem N K)) K = true)
    (hv : ∀ v t, MV v → Keep tailRegs v t → KBase B Z s0 t →
      t.gpr .a4 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem E L))) <<< 31 →
      Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem E L)) = true →
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem N K)) K = true →
      WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ loads ++ body ++ ([.block ret] : List (Prog isa)))) t fun u =>
        KBase B Z s0 u ∧ u.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    WP isa (fn (8 * oS) moves loads body) s0 fun t =>
      (∀ i < 12, t.gpr (saved i) = s0.gpr (saved i)) ∧ t.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0) := by
  have hZ : 96 ≤ Z := by have := hp.zk; omega
  have hs : Scr s0 (stackArg s0 oS) Z := by rw [hp.base]; exact Scr.of_mem hp.wr hp.nowrap hp.al
  unfold fn
  rw [entry_eq]
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s0 hoS (hp.arg_rd hp.hoS) (hp.arg_al hp.hoS) hs hZ) fun u hu => ?_
  rw [hp.base] at hu
  have bu := KBase.of_saved hu hZ
  refine WP.mono (hm u hu) fun v ⟨mv, vm, vrd, vwr, v11, v4, v5, v1, v2⟩ => ?_
  have bv : KBase B Z s0 v := ⟨vrd.trans bu.rd, vwr.trans bu.wr, fun x hx => by rw [vm]; exact bu.frame x hx,
    fun i hi => by rw [vm]; exact bu.hdr i hi, v11.trans bu.s11⟩
  have rdv : ∀ {P : Addr} {M : Nat}, (⟨P, M⟩ : Region) ∈ s0.rd → P.toNat + M ≤ 2 ^ 64 → ∀ i < M,
      InRegions (v.rd ++ v.wr) (off P i) 1 := fun hP wP i hi =>
    ⟨_, List.mem_append_left _ (by rw [bv.rd]; exact hP), Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (tail_ok v4 v5 hL hL' (rdv hE wE) v1 v2 hp.k64 hp.k1024 (rdv hN wN))
    fun t ⟨t0, t4, tm, kt⟩ => ?_
  rw [bytes_frame bv dE wE, bytes_frame bv dN wN] at t0
  rw [bytes_frame bv dE wE] at t4
  have bt := bv.of_regs kt tm
  have fin : ∀ u, KBase B Z s0 u → u.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0) →
      WP isa (.block restore) u fun x =>
        (∀ i < 12, x.gpr (saved i) = s0.gpr (saved i)) ∧ x.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0) := by
    intro u bu' a0
    have hsu : Scr u B Z := Scr.of_mem (by rw [bu'.wr]; exact hp.wr) hp.nowrap hp.al
    refine WP.mono (restore_ok u hsu hZ bu'.s11 bu'.hdr) fun x ⟨xs, xo, _⟩ => ⟨xs, ?_⟩
    rw [xo .a0 (by decide), a0]
  refine WP.seq ?_
  refine WP.ite _ (Steps.eval_zero t .t0) (fun hz => ?_) (fun hz => ?_)
  · have hz' : t.gpr .t0 = 0 := by simpa using hz
    obtain ⟨ev, mv'⟩ := t0.mp hz'
    exact WP.mono (hv v t mv kt bt t4 ev mv') fun u ⟨bu', a0⟩ => fin u bu' a0
  · have hz' : t.gpr .t0 ≠ 0 := by simpa using hz
    have hok' : ok = false := by
      cases e : ok
      · rfl
      · exact absurd (t0.mpr (hok e)) hz'
    refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 0 ∧ u.mem = t.mem) (by
      have e : exec (.li .a0 0) t = some (t.write .a0 (BitVec.ofNat 64 0)) := by
        rw [exec_li (by decide)]; rfl
      brun [ret0, e]) (by rfl) (by rfl)) fun u ⟨⟨a0, um⟩, ku⟩ => fin u (bt.of_regs ku um) ?_
    rw [a0, hok']; rfl

/-- The checks keep `KBase`. -/
theorem Stg.base {g : Geo} {s0 sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) (hb : KBase g.B g.Z s0 sS) : KBase g.B g.Z s0 t :=
  hb.of_frame h.frame (fun j hj => h.ws.arr_fit (List.mem_range.mp hj)) (by decide) h.ws.hdr_le h.regs

/-- `ret`: the mask's bit in `a0`. -/
theorem ret_ok {g : Geo} {sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) :
    WP isa (.block ret) t fun u => (u.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0) ∧ u.mem = t.mem) ∧
      Keep [.a0] t u := by
  have hs := h.ws.scr
  have hz := h.ws.hdr_le
  have e : word t.mem g.B sMask = BitVec.ofNat 64 (if c then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by cases c <;> decide)]
    exact h.mask
  have ea : t.gpr .s11 + BitVec.ofNat 64 sMask = off g.B sMask := by rw [h.ws.s11]
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .s11 + BitVec.ofNat 64 sMask) 8 := by
    rw [ea]; exact hs.ld (d := sMask) (n := 8) (by simp only [hdr_eq] at hz; unfold sMask; omega)
  have hal : (t.gpr .s11 + BitVec.ofNat 64 sMask).toNat % 8 = 0 := by
    rw [ea]; exact hs.al8 (d := sMask) (by simp only [hdr_eq] at hz; unfold sMask; omega) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) hal hin, WP.block_nil ?_⟩
  rw [ea]
  exact ⟨by rw [gpr_write_self]; exact e, rfl⟩

end VG.Proof.Rsa.RISCV64.KeyCheck
