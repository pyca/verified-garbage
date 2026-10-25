module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Pre
public import VerifiedGarbage.Proof.AesXts.X86.Steps
public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.MdStream.X86.Common
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.CmacAes.X86.Save
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# XTS-AES of data units on x86: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_ok`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`). The pieces reload the arguments from
the stack, which they need unchanged (`ArgsOk`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_sub wp_shr wp_movzx8
  wp_store8 ea_at)
open VG.Proof.CmacAes.X86 (wp_arg wp_addArg ea_at')
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

/-- `s'` is `s` with memory `m`, and only the registers `rs` changed (and the flags). -/
structure Chg (s s' : State) (rs : List Reg) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Chg.refl (s : State) (rs : List Reg) : Chg s s rs s.mem := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Chg.upd {s s₁ s' : State} {rs : List Reg} {m : Mem} (h : Chg s s₁ rs m) {d : Reg} {v : BitVec 32}
    (u : Upd s₁ s' d v) (hd : d ∈ rs) : Chg s s' rs m :=
  ⟨fun r hr => by rw [u.other r (fun e => hr (e ▸ hd)), h.gpr r hr], by rw [u.mem, h.mem], by rw [u.rd, h.rd],
    by rw [u.wr, h.wr]⟩

theorem Chg.mupd {s s₁ s' : State} {rs : List Reg} {m m' : Mem} (h : Chg s s₁ rs m) (u : Mupd s₁ s' m') :
    Chg s s' rs m' :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, by rw [u.rd, h.rd], by rw [u.wr, h.wr]⟩

theorem Chg.mono {s s' : State} {rs rs' : List Reg} {m : Mem} (h : Chg s s' rs m) (hs : ∀ r ∈ rs, r ∈ rs') :
    Chg s s' rs' m :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr⟩

/-- The stack arguments of the entry state `s₀`, readable and unchanged in `s`. -/
structure ArgsOk (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  inr : ∀ i < 7, InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4
  val : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem ArgsOk.upd {s₀ s s' : State} (h : ArgsOk s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .esp) : ArgsOk s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd), h.esp], by rw [u.rd, u.wr]; exact h.inr, by rw [u.mem]; exact h.val⟩

/-- `mov d, [esp + 4 + 4 i]`. -/
theorem wp_argA {is : List Instr} {s₀ s : State} {Q : State → Prop} {d : Reg} {i : Nat} (h : ArgsOk s₀ s)
    (hi : i < 7) (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  wp_arg h.esp (h.inr i hi) (h.val i hi) k

/-- `add d, [esp + 4 + 4 i]`. -/
theorem wp_addArgA {is : List Instr} {s₀ s : State} {Q : State → Prop} {d : Reg} {i : Nat} (h : ArgsOk s₀ s)
    (hi : i < 7) (k : ∀ s', Upd s s' d (s.gpr d + arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (argOp i) :: is)) s Q :=
  wp_addArg h.esp (h.inr i hi) (h.val i hi) k

/-- `and d, imm`, and ZF. -/
theorem wp_andiZ {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.X86.WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _) rfl)

/-! ## The arguments, from the precondition -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.argA {i : Nat} (hi : i < 7) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by simp only [E] at this; omega_arith), addr_eq (by simp only [E] at this; omega_arith), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_arith)

theorem UPre.arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The arguments, where only the data, the scratch buffer and the stack
below `esp` have changed. -/
theorem UPre.argsOk {s : State} (hesp : s.gpr .esp = s₀.gpr .esp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [dataR s₀, scrR s₀, stkR s₀] s₀.mem s.mem) : ArgsOk s₀ s where
  esp := hesp
  inr i hi := by rw [hrd, hwr]; exact hp.arg_in hi
  val i hi := hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.scr_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.stk_args.symm.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.argsOk₀ : ArgsOk s₀ s₀ := ⟨rfl, fun _ hi => hp.arg_in hi, fun _ _ => rfl⟩

/-- The arguments, across writes to regions apart from them. -/
theorem UPre.argsOk_frame {s s' : State} (h : ArgsOk s₀ s) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (argsR s₀).Disjoint r) :
    ArgsOk s₀ s' where
  esp := by rw [hesp, h.esp]
  inr i hi := by rw [hrd, hwr]; exact h.inr i hi
  val i hi := by
    rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (hp.arg_sub hi)) (by decide)]
    exact h.val i hi

end

theorem r_ofNat (s₀ : State) : BitVec.ofNat 32 (R s₀) = arg s₀ 2 := by simp [R]

/-! ## Blocks of words -/

/-- The block at `Q` copied to `P`, a word at a time, read before any is written. -/
def copy4 (m : Mem) (P Q : Addr) : Mem :=
  Proof.Cmac.store4 m P (m.readW Q 32) (m.readW (Q + BitVec.ofNat 64 4) 32) (m.readW (Q + BitVec.ofNat 64 8) 32)
    (m.readW (Q + BitVec.ofNat 64 12) 32)

theorem copy4_frame (m : Mem) (P Q : Addr) : Frame [⟨P, 16⟩] m (copy4 m P Q) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem copy4_bytes (m : Mem) (P Q : Addr) : bytesAt (copy4 m P Q) P 16 = bytesAt m Q 16 := by
  rw [copy4, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

/-- A write within a block keeps the words of a disjoint one. -/
theorem readW_sep {m : Mem} {P Q : Addr} (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩) {k : Nat} (hk : k ≤ 12)
    (w : BitVec 32) {j : Nat} (hj : j ≤ 12) :
    (m.writeW (P + BitVec.ofNat 64 j) w).readW (Q + BitVec.ofNat 64 k) 32 = m.readW (Q + BitVec.ofNat 64 k) 32 := by
  refine ((Frame.refl _ _).writeW (rs := [⟨P, 16⟩]) (List.mem_singleton_self _) w
    (Offset.contains_base P (d := j) (n := 4) (k := 16) (by omega_arith) (by omega_arith))).readW
    (r := ⟨Q + BitVec.ofNat 64 k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (hpq.symm.sub_left (Offset.sub_base Q (d := k) (n := 4) (k := 16) (by omega_arith)))

theorem readW_sep0 {m : Mem} {P Q : Addr} (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩) {k : Nat} (hk : k ≤ 12)
    (w : BitVec 32) : (m.writeW P w).readW (Q + BitVec.ofNat 64 k) 32 = m.readW (Q + BitVec.ofNat 64 k) 32 := by
  have := readW_sep (m := m) hpq hk w (j := 0) (by decide); simpa using this

/-- `copy r dst d src e` of disjoint blocks: the source's words through `r`. -/
theorem copy_wp {s : State} {r dst src : Reg} {d e : Nat} {P Q : Addr} {is : List Instr} {Φ : State → Prop}
    (hr₁ : r ≠ dst) (hr₂ : r ≠ src)
    (hq : (s.gpr src).setWidth 64 + BitVec.ofNat 64 e = Q) (hqf : (s.gpr src).toNat + e + 16 ≤ 2 ^ 32)
    (hp : (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d = P) (hpf : (s.gpr dst).toNat + d + 16 ≤ 2 ^ 32)
    (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩)
    (hrd : ∀ k n, k + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 k) n)
    (hwr : ∀ k n, k + n ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 k) n)
    (k : ∀ s', Chg s s' [r] (copy4 s.mem P Q) → WP isa (.block is) s' Φ) :
    WP isa (.block (copy r dst d src e ++ is)) s Φ := by
  have a (k : Nat) (hk : k ≤ 12) : addr (s.gpr src) (e + k) = Q + BitVec.ofNat 64 k := by
    rw [addr_eq (by omega_arith), ← Offset.add_add, hq]
  have b (k : Nat) (hk : k ≤ 12) : addr (s.gpr dst) (d + k) = P + BitVec.ofNat 64 k := by
    rw [addr_eq (by omega_arith), ← Offset.add_add, hp]
  have a0 : addr (s.gpr src) e = Q := by rw [addr_eq (by omega_arith), hq]
  have b0 : addr (s.gpr dst) d = P := by rw [addr_eq (by omega_arith), hp]
  have rq (k : Nat) (hk : k ≤ 12) : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 k) 4 := hrd k 4 (by omega_arith)
  have wp (k : Nat) (hk : k ≤ 12) : InRegions s.wr (P + BitVec.ofNat 64 k) 4 := hwr k 4 (by omega_arith)
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using rq 0 (by decide)
  have w0 : InRegions s.wr P 4 := by simpa using wp 0 (by decide)
  simp only [copy, List.cons_append, List.nil_append]
  refine wp_movm (a := Q) (by rw [ea_at']; exact a0) r0 fun s₁ u₁ => ?_
  have c₁ := (Chg.refl s [r]).upd u₁ (List.mem_singleton_self _)
  refine wp_store (a := P) (by rw [ea_at', c₁.gpr _ (by simpa using hr₁.symm)]; exact b0)
    (by rw [c₁.wr]; exact w0) fun s₂ u₂ => ?_
  have c₂ := c₁.mupd u₂
  have m₂ : s₂.mem = s.mem.writeW P (s.mem.readW Q 32) := by rw [u₂.mem, u₁.gpr, u₁.mem]
  refine wp_movm (a := Q + BitVec.ofNat 64 4) (by rw [ea_at', c₂.gpr _ (by simpa using hr₂.symm)]; exact a 4 (by decide))
    (by rw [c₂.rd, c₂.wr]; exact rq 4 (by decide)) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (List.mem_singleton_self _)
  have v₃ : s₃.gpr r = s.mem.readW (Q + BitVec.ofNat 64 4) 32 := by rw [u₃.gpr, m₂, readW_sep0 hpq (by decide)]
  refine wp_store (a := P + BitVec.ofNat 64 4) (by rw [ea_at', c₃.gpr _ (by simpa using hr₁.symm)]; exact b 4 (by decide))
    (by rw [c₃.wr]; exact wp 4 (by decide)) fun s₄ u₄ => ?_
  have c₄ := c₃.mupd u₄
  have m₄ : s₄.mem = (s.mem.writeW P (s.mem.readW Q 32)).writeW (P + BitVec.ofNat 64 4)
      (s.mem.readW (Q + BitVec.ofNat 64 4) 32) := by rw [u₄.mem, v₃, u₃.mem, m₂]
  refine wp_movm (a := Q + BitVec.ofNat 64 8) (by rw [ea_at', c₄.gpr _ (by simpa using hr₂.symm)]; exact a 8 (by decide))
    (by rw [c₄.rd, c₄.wr]; exact rq 8 (by decide)) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (List.mem_singleton_self _)
  have v₅ : s₅.gpr r = s.mem.readW (Q + BitVec.ofNat 64 8) 32 := by
    rw [u₅.gpr, m₄, readW_sep hpq (by decide) _ (by decide), readW_sep0 hpq (by decide)]
  refine wp_store (a := P + BitVec.ofNat 64 8) (by rw [ea_at', c₅.gpr _ (by simpa using hr₁.symm)]; exact b 8 (by decide))
    (by rw [c₅.wr]; exact wp 8 (by decide)) fun s₆ u₆ => ?_
  have c₆ := c₅.mupd u₆
  have m₆ : s₆.mem = ((s.mem.writeW P (s.mem.readW Q 32)).writeW (P + BitVec.ofNat 64 4)
      (s.mem.readW (Q + BitVec.ofNat 64 4) 32)).writeW (P + BitVec.ofNat 64 8)
      (s.mem.readW (Q + BitVec.ofNat 64 8) 32) := by rw [u₆.mem, v₅, u₅.mem, m₄]
  refine wp_movm (a := Q + BitVec.ofNat 64 12) (by rw [ea_at', c₆.gpr _ (by simpa using hr₂.symm)]; exact a 12 (by decide))
    (by rw [c₆.rd, c₆.wr]; exact rq 12 (by decide)) fun s₇ u₇ => ?_
  have c₇ := c₆.upd u₇ (List.mem_singleton_self _)
  have v₇ : s₇.gpr r = s.mem.readW (Q + BitVec.ofNat 64 12) 32 := by
    rw [u₇.gpr, m₆, readW_sep hpq (by decide) _ (by decide), readW_sep hpq (by decide) _ (by decide),
      readW_sep0 hpq (by decide)]
  refine wp_store (a := P + BitVec.ofNat 64 12) (by rw [ea_at', c₇.gpr _ (by simpa using hr₁.symm)]; exact b 12 (by decide))
    (by rw [c₇.wr]; exact wp 12 (by decide)) fun s₈ u₈ => k s₈ ?_
  refine ⟨(c₇.mupd u₈).gpr, ?_, (c₇.mupd u₈).rd, (c₇.mupd u₈).wr⟩
  rw [u₈.mem, v₇, u₇.mem, m₆]; rfl

/-! ## The arguments of the calls -/

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_arith)]

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : BitVec 32) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 32 (16 * m) - 16 = p + BitVec.ofNat 32 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem UPre.lv_eq {s₀ : State} (hp : UPre s₀) : arg s₀ 5 - BitVec.ofNat 32 (B s₀) + D s₀ - 16 = Lv s₀ := by
  have hm := hp.m_pos
  have e := len_eq s₀
  rw [show arg s₀ 5 = BitVec.ofNat 32 (Len s₀) by simp [Len], MdStream.X86.sub_ofNat (by omega_arith),
    show Len s₀ - B s₀ = 16 * M s₀ by omega_arith, BitVec.add_comm, Lv, last_eq _ hm]

section
variable {s₀ s : State} {is : List Instr} {Φ : State → Prop} (h : ArgsOk s₀ s)
include h

/-- The arguments of a call on the `len / 16` whole blocks from the tweak. -/
theorem argsAll_wp
    (k : ∀ s', Chg s s' xRegs s.mem → s'.gpr .eax = W s₀ → s'.gpr .ecx = arg s₀ 2 →
      s'.gpr .edx = S s₀ + BitVec.ofNat 32 tO → s'.gpr .ebx = D s₀ → s'.gpr .edi = BitVec.ofNat 32 (M s₀) →
      s'.gpr .ebp = S s₀ → WP isa (.block is) s' Φ) :
    WP isa (.block (argsAll ++ is)) s Φ := by
  simp only [argsAll, List.cons_append, List.nil_append]
  refine wp_argA h (i := 6) (by decide) fun s₁ u₁ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_argA h₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  refine wp_argA h₂ (i := 2) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  have h₅ := (h₃.upd u₄ (by decide)).upd u₅ (by decide)
  refine wp_argA h₅ (i := 4) (by decide) fun s₆ u₆ => ?_
  have h₆ := h₅.upd u₆ (by decide)
  refine wp_argA h₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  refine wp_shr (n := 4) (by decide) fun s₈ u₈ => ?_
  have c := (((((((((Chg.refl s xRegs).upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide))
  refine k s₈ c ?_ ?_ ?_ ?_ ?_ ?_
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, u₁.gpr]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr]
  · rw [u₈.gpr, u₇.gpr, shr4]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]

/-- The arguments of a call on all but the last whole block. -/
theorem argsHead_wp (hm : 1 ≤ M s₀)
    (k : ∀ s', Chg s s' xRegs s.mem → s'.gpr .eax = W s₀ → s'.gpr .ecx = arg s₀ 2 →
      s'.gpr .edx = S s₀ + BitVec.ofNat 32 tO → s'.gpr .ebx = D s₀ →
      s'.gpr .edi = BitVec.ofNat 32 (M s₀ - 1) → s'.gpr .ebp = S s₀ → WP isa (.block is) s' Φ) :
    WP isa (.block (argsHead ++ is)) s Φ := by
  rw [argsHead, List.append_assoc, List.cons_append, List.nil_append]
  refine argsAll_wp h fun s₁ c₁ ax cx dx bx di bp => wp_subi fun s₂ u₂ _ => ?_
  refine k s₂ (c₁.upd u₂ (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [u₂.other _ (by decide), ax]
  · rw [u₂.other _ (by decide), cx]
  · rw [u₂.other _ (by decide), dx]
  · rw [u₂.other _ (by decide), bx]
  · rw [u₂.gpr, di]; exact MdStream.X86.ofNat_pred hm
  · rw [u₂.other _ (by decide), bp]

/-- `b = len mod 16` into `esi`, and ZF set if it is zero. -/
theorem split_wp
    (k : ∀ s', Chg s s' [.esi] s.mem → s'.gpr .esi = BitVec.ofNat 32 (B s₀) → s'.zf = some (decide (B s₀ = 0)) →
      WP isa (.block is) s' Φ) :
    WP isa (.block (split ++ is)) s Φ := by
  simp only [split, List.cons_append, List.nil_append]
  refine wp_argA h (i := 5) (by decide) fun s₁ u₁ => wp_andiZ fun s₂ u₂ z₂ => ?_
  have e : s₁.gpr .esi &&& 15 = BitVec.ofNat 32 (B s₀) := by rw [u₁.gpr, and15]
  refine k s₂ (((Chg.refl s _).upd u₁ (by decide)).upd u₂ (by decide)) (by rw [u₂.gpr, e]) ?_
  rw [z₂, e, MdStream.X86.ofNat_beq_zero (by simp only [B]; omega_arith)]

variable (hp : UPre s₀) (hsi : s.gpr .esi = BitVec.ofNat 32 (B s₀))
include hp hsi

/-- The address of the last whole block into `edx`, and `b` into `ecx`. -/
theorem lastAddr_wp
    (k : ∀ s', Chg s s' [.edx, .ecx] s.mem → s'.gpr .edx = Lv s₀ → s'.gpr .ecx = BitVec.ofNat 32 (B s₀) →
      WP isa (.block is) s' Φ) :
    WP isa (.block (lastAddr ++ is)) s Φ := by
  simp only [lastAddr, List.cons_append, List.nil_append]
  refine wp_argA h (i := 5) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ _ => ?_
  have h₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_argA h₂ (i := 4) (by decide) fun s₃ u₃ => MdStream.X86.wp_add fun s₄ u₄ => wp_subi fun s₅ u₅ _ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  refine k s₆ ((((((Chg.refl s _).upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide) |>.upd u₅ (by decide)).upd u₆ (by decide)) ?_ ?_
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), hsi]
    exact hp.lv_eq
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hsi]

/-- The arguments of a call on the last whole block, from the tweak at `o`. -/
theorem argsL_wp {o : Nat}
    (k : ∀ s', Chg s s' xRegs s.mem → s'.gpr .eax = W s₀ → s'.gpr .ecx = arg s₀ 2 →
      s'.gpr .edx = S s₀ + BitVec.ofNat 32 o → s'.gpr .ebx = Lv s₀ → s'.gpr .edi = BitVec.ofNat 32 1 →
      s'.gpr .ebp = S s₀ → WP isa (.block is) s' Φ) :
    WP isa (.block (argsL o ++ is)) s Φ := by
  simp only [argsL, List.cons_append, List.nil_append]
  refine wp_argA h (i := 5) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ _ => ?_
  have h₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_addArgA h₂ (i := 4) (by decide) fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  have h₄ := (h₂.upd u₃ (by decide)).upd u₄ (by decide)
  refine wp_argA h₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  have h₅ := h₄.upd u₅ (by decide)
  refine wp_argA h₅ (i := 0) (by decide) fun s₆ u₆ => ?_
  have h₆ := h₅.upd u₆ (by decide)
  refine wp_argA h₆ (i := 2) (by decide) fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_addi fun s₉ u₉ => ?_
  refine wp_movi fun s₁₀ u₁₀ => ?_
  have c := (((((((((((Chg.refl s xRegs).upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉
    (by decide)).upd u₁₀ (by decide))
  refine k s₁₀ c ?_ ?_ ?_ ?_ u₁₀.gpr ?_
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr]
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.gpr]
  · simp (disch := decide) only [u₁₀.other, u₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.gpr]
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other]
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hsi]
    exact hp.lv_eq
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr]

end

/-! ## The swap -/

theorem in_wr {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) : InRegions (rs ++ ws) a n :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

theorem byte_rt (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem addr_k {x : BitVec 32} {L : Addr} (hx : x.setWidth 64 = L) {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = L + BitVec.ofNat 64 (k + d) := by
  rw [show addr (x + BitVec.ofNat 32 k) d = addr x (k + d) by simp only [addr, MdStream.X86.ofNat_add_add],
    addr_eq (by omega_arith), hx]

/-- The first `b` bytes of the block at `L` (in `edx`) swapped with the `b`
bytes after it (`b` in `ecx`). -/
theorem swap_ok (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : (s.gpr .edx).setWidth 64 = L)
    (hxf : (s.gpr .edx).toNat + 16 + b ≤ 2 ^ 32) (hc : s.gpr .ecx = BitVec.ofNat 32 b)
    (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => Chg s s' [.eax, .ebx, .ecx, .edx] (swapMem s.mem L b) := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .edx = s.gpr .edx + BitVec.ofNat 32 k ∧
      t.gpr .ecx = BitVec.ofNat 32 (b - k) ∧ Chg s t [.eax, .ebx, .ecx, .edx] (swapMem s.mem L k)) ?_ (b - 0) _
    ⟨0, rfl, hb₀, (BitVec.add_zero _).symm, hc,
      ⟨fun _ _ => rfl, (Proof.AesXts.Unit.swapMem_zero _ _).symm, rfl, rfl⟩⟩
  rintro n t ⟨k, rfl, hk, xdx, xcx, ct⟩
  have hlo : t.mem (L + BitVec.ofNat 64 k) = s.mem (L + BitVec.ofNat 64 k) := by
    rw [ct.mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_arith)]
  have hhi : t.mem (L + BitVec.ofNat 64 (16 + k)) = s.mem (L + BitVec.ofNat 64 (16 + k)) := by
    rw [ct.mem, swapMem_hi _ _ (Nat.le_refl k) (by omega_arith)]
  have in₀ : InRegions t.wr (L + BitVec.ofNat 64 k) 1 := by rw [ct.wr]; exact hw k (by omega_arith)
  have in₁ : InRegions t.wr (L + BitVec.ofNat 64 (16 + k)) 1 := by rw [ct.wr]; exact hw (16 + k) (by omega_arith)
  have a₀ : t.ea (at_ .edx 0) = L + BitVec.ofNat 64 k := by
    rw [ea_at', xdx, addr_k hx (by omega_arith), Nat.add_zero]
  have a₁ (t' : State) (he : t'.gpr .edx = t.gpr .edx) : t'.ea (at_ .edx 16) = L + BitVec.ofNat 64 (16 + k) := by
    rw [ea_at', he, xdx, addr_k hx (by omega_arith), Nat.add_comm]
  refine wp_movzx8 a₀ (in_wr in₀) fun t₁ u₁ => ?_
  refine wp_movzx8 (a₁ t₁ (u₁.other _ (by decide))) (by rw [u₁.rd, u₁.wr]; exact in_wr in₁) fun t₂ u₂ => ?_
  refine wp_store8 (a := L + BitVec.ofNat 64 k) (by rw [ea_at', u₂.other _ (by decide), u₁.other _ (by decide)]; exact a₀)
    (by rw [u₂.wr, u₁.wr]; exact in₀) fun t₃ v₃ => ?_
  refine wp_store8 (a₁ t₃ (by rw [v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]))
    (by rw [v₃.wr, u₂.wr, u₁.wr]; exact in₁) fun t₄ v₄ => ?_
  refine wp_addi fun t₅ u₅ => wp_subi fun t₆ u₆ z₆ => WP.block_nil ?_
  have bl : t₂.gpr Reg8.bl.reg = (t.mem (L + BitVec.ofNat 64 (16 + k))).setWidth 32 := by
    rw [show Reg8.bl.reg = Reg.ebx from rfl, u₂.gpr, u₁.mem]
  have al : t₃.gpr Reg8.al.reg = (t.mem (L + BitVec.ofNat 64 k)).setWidth 32 := by
    rw [show Reg8.al.reg = Reg.eax from rfl, v₃.gpr, u₂.other _ (by decide), u₁.gpr]
  have hmem : t₆.mem = swapMem s.mem L (k + 1) := by
    rw [u₆.mem, u₅.mem, v₄.mem, al, v₃.mem, bl, u₂.mem, u₁.mem, byte_rt, byte_rt, hlo, hhi, ct.mem,
      swapMem_step _ _ (by omega_arith)]
  have cx₅ : t₅.gpr .ecx = BitVec.ofNat 32 (b - k) := by
    rw [u₅.other _ (by decide), v₄.gpr, v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), xcx]
  have ev : isa.eval .ne t₆ = some !decide (b - (k + 1) = 0) := by
    show VG.X86.eval .ne t₆ = _
    rw [MdStream.X86.eval_ne, z₆, cx₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.X86.sub_ofNat (by omega_arith), Nat.sub_sub, MdStream.X86.ofNat_beq_zero (by omega_arith)]
    rfl
  have c₆ : Chg s t₆ [.eax, .ebx, .ecx, .edx] (swapMem s.mem L (k + 1)) :=
    ⟨fun r hr => by
      have h₁ : r ≠ .eax := fun e => hr (by simp [e])
      have h₂ : r ≠ .ebx := fun e => hr (by simp [e])
      have h₃ : r ≠ .ecx := fun e => hr (by simp [e])
      have h₄ : r ≠ .edx := fun e => hr (by simp [e])
      rw [u₆.other _ h₃, u₅.other _ h₄, v₄.gpr, v₃.gpr, u₂.other _ h₂, u₁.other _ h₁, ct.gpr r hr], hmem,
      by rw [u₆.rd, u₅.rd, v₄.rd, v₃.rd, u₂.rd, u₁.rd, ct.rd], by rw [u₆.wr, u₅.wr, v₄.wr, v₃.wr, u₂.wr, u₁.wr, ct.wr]⟩
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [ev]; simp [he], ?_⟩
    rw [← he]; exact c₆
  · right
    refine ⟨by rw [ev]; simp; omega_arith, b - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, ?_, ?_, c₆⟩
    · rw [u₆.other _ (by decide), u₅.gpr, v₄.gpr, v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), xdx,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
    · rw [u₆.gpr, cx₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.X86.sub_ofNat (by omega_arith),
        Nat.sub_sub]

/-! ## The next tweak -/

section
variable (s₀ : State)

/-- The tweak and the second tweak, as addresses and as register values. -/
abbrev Tp : Addr := Sa s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := Sa s₀ + BitVec.ofNat 64 zO
abbrev Tv : BitVec 32 := S s₀ + BitVec.ofNat 32 tO
abbrev Zv : BitVec 32 := S s₀ + BitVec.ofNat 32 zO

end

theorem nextT_wp {s₀ s : State} {is : List Instr} {Φ : State → Prop} (hp : UPre s₀) (h : ArgsOk s₀ s)
    (hwr : s.wr = s₀.wr)
    (k : ∀ s', Chg s s' [.eax, .ecx, .edx, .ebx, .edi, .ebp] (Proof.AesXts.X86.alphaMem (copy4 s.mem (Zp s₀) (Tp s₀))
      (Zp s₀)) → WP isa (.block is) s' Φ) :
    WP isa (.block (nextT ++ is)) s Φ := by
  have hsc : (arg s₀ 6).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  rw [nextT, List.append_assoc, List.append_assoc, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_argA h (i := 6) (by decide) fun s₁ u₁ => ?_
  have inS (d n : Nat) (hd : d + n ≤ 2432) : InRegions s₁.wr (Sa s₀ + BitVec.ofNat 64 d) n := by
    rw [u₁.wr, hwr, hp.wr]; exact ⟨scrR s₀, by simp, hp.cS d n hd⟩
  refine copy_wp (P := Zp s₀) (Q := Tp s₀) (by decide) (by decide) (by rw [u₁.gpr]) (by rw [u₁.gpr]; simp only [tO]; omega_arith)
    (by rw [u₁.gpr]) (by rw [u₁.gpr]; simp only [zO]; omega_arith) hp.t_z.symm
    (fun d n hd => by
      obtain ⟨r, hr, c⟩ := inS (tO + d) n (by simp only [tO]; omega_arith)
      exact ⟨r, List.mem_append_right _ hr, by rw [Offset.add_add]; exact c⟩)
    (fun d n hd => by rw [Offset.add_add]; exact inS (zO + d) n (by simp only [zO]; omega_arith)) fun s₂ c₂ => ?_
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  have bx : s₄.gpr .ebx = Zv s₀ := by
    rw [u₄.gpr, u₃.gpr, c₂.gpr _ (by decide), u₁.gpr]
  have wr₄ : s₄.wr = s₁.wr := by rw [u₄.wr, u₃.wr, c₂.wr]
  have rd₄ : s₄.rd = s₁.rd := by rw [u₄.rd, u₃.rd, c₂.rd]
  obtain ⟨s₅, run₅, g₅, m₅, rd₅, wr₅⟩ := Proof.AesXts.X86.mulA_ok s₄ (Q := Zp s₀) (by rw [bx]; exact hp.scrW (by decide))
    (by rw [bx, hp.scrN (by decide)]; have := hp.scr_fit; simp only [zO]; omega_arith)
    (fun d n hd => by
      rw [rd₄, wr₄]
      obtain ⟨r, hr, c⟩ := inS (zO + d) n (by simp only [zO]; omega_arith)
      exact ⟨r, List.mem_append_right _ hr, by rw [Offset.add_add]; exact c⟩)
    (fun d n hd => by rw [wr₄, Offset.add_add]; exact inS (zO + d) n (by simp only [zO]; omega_arith))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₅, run₅, k s₅ ⟨fun r hr => ?_, ?_, ?_, ?_⟩⟩)
  · have h₁ : r ≠ .eax := fun e => hr (by simp [e])
    have h₂ : r ≠ .ecx := fun e => hr (by simp [e])
    have h₃ : r ≠ .edx := fun e => hr (by simp [e])
    have h₄ : r ≠ .ebx := fun e => hr (by simp [e])
    have h₅ : r ≠ .edi := fun e => hr (by simp [e])
    have h₆ : r ≠ .ebp := fun e => hr (by simp [e])
    rw [g₅ r h₁ h₂ h₃ h₅ h₆, u₄.other _ h₄, u₃.other _ h₄, c₂.gpr r (by simpa using h₁), u₁.other _ h₆]
  · rw [m₅, u₄.mem, u₃.mem, c₂.mem, u₁.mem]
  · rw [rd₅, rd₄, u₁.rd]
  · rw [wr₅, wr₄, u₁.wr]

end VG.Proof.AesXts.X86.Unit
