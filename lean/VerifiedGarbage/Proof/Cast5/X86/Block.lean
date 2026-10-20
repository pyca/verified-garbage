module

public import VerifiedGarbage.Proof.Cast5.X86.Round
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# CAST5 on 32-bit x86: a block

The rounds of a block, three at a time (`group`), and `crypt`: from the block
at the data slot of the working space to its encryption or decryption there,
under the subkeys and the number of rounds in their slots.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym)
open VG.Proof.Cast5 (tableEnt encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq
  roundI decodeBlock_blockAt blockAt_write)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

/-- The S-box table of the rounds. -/
abbrev tab1234 : Nat → Nat → BitVec 32 := tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1

/-- The memory a block's rounds write. -/
def blockMem (S sp : BitVec 32) : List Region := [below sp 4, slotR S 0 16, slotR S kpOff 8]

/-- What every round of a block reads: the working space at `S` (`esi`), its
slots holding the subkeys' address `K` and the number of rounds `n`, the
subkeys `k` at `K`, the table, and the word below `esp`, apart from each
other. -/
structure Ctx (s : State) (S K : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  si : s.gpr .esi = S
  fitS : S.toNat + 256 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  schedSlot : s.mem.readW (addr S schedOff) 32 = K
  roundsSlot : s.mem.readW (addr S roundsOff) 32 = BitVec.ofNat 32 n
  nv : n = 12 ∨ n = 16
  fitK : K.toNat + 128 ≤ 2 ^ 32
  inK : InRegions (s.rd ++ s.wr) (K.setWidth 64) 128
  key : ∀ j < 32, s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  sp : 4 ≤ (s.gpr .esp).toNat
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨K.setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dKS : Region.Disjoint ⟨K.setWidth 64, 128⟩ ⟨S.setWidth 64, 256⟩
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  dTS : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨S.setWidth 64, 256⟩
  tab : TabAt s.mem (s.syms s1234Sym) tab1234

/-- A slot region inside the working space. -/
theorem slot_sub (S : BitVec 32) {d n : Nat} (h : d + n ≤ 256) : Region.Sub (slotR S d n) ⟨S.setWidth 64, 256⟩ :=
  Offset.sub_base _ h

/-- The regions a block writes miss the subkeys, the table and the slots
`48 … 63`. -/
theorem blockMem_disjoint {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n) :
    ∀ r ∈ blockMem S (s.gpr .esp), r.Disjoint ⟨K.setWidth 64, 128⟩ ∧
      r.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ∧ r.Disjoint (slotR S 48 16) := by
  intro r hr
  simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨h.dK.symm, h.dT.symm, (h.dS.sub_left (slot_sub S (by decide))).symm⟩
  · exact ⟨(h.dKS.sub_right (slot_sub S (by decide))).symm, (h.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · exact ⟨(h.dKS.sub_right (slot_sub S (by decide))).symm, (h.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩

/-- A slot of `48 … 63`, read through a frame missing them. -/
theorem slot_frame {m m' : Mem} {rs : List Region} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, r.Disjoint (slotR S 48 16)) {d : Nat} (h1 : 48 ≤ d) (h2 : d + 4 ≤ 64) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 := by
  rw [addr_off hfit d (by omega)]
  exact hf.readW (r := slotR S 48 16) (Offset.contains _ h1 (by omega) (by omega))
    (fun r hr => (hd r hr).symm) (by decide)

/-- The context holds in a state that differs only in the registers but
`esi` and `esp`, and in memory missing the subkeys, the table and the slots
`48 … 63`. -/
theorem Ctx.transfer {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    (hsi : u.gpr .esi = S) (hsp : u.gpr .esp = s.gpr .esp) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsy : u.syms = s.syms) {rs : List Region} (hf : Frame rs s.mem u.mem)
    (hd : ∀ r ∈ rs, r.Disjoint ⟨K.setWidth 64, 128⟩ ∧ r.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ∧
      r.Disjoint (slotR S 48 16)) :
    Ctx u S K k n := by
  refine ⟨hsi, h.fitS, by rw [hwr]; exact h.wS, ?_, ?_, h.nv, h.fitK, by rw [hrd, hwr]; exact h.inK,
    fun j hj => ?_, by rw [hsp]; exact h.sp, by rw [hsp]; exact h.dS, by rw [hsp]; exact h.dK, h.dKS,
    by rw [hsy]; exact h.fitT, by rw [hrd, hwr, hsy]; exact h.inT, by rw [hsy, hsp]; exact h.dT,
    by rw [hsy]; exact h.dTS, fun j hj q hq => ?_⟩
  · rw [slot_frame h.fitS hf (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact h.schedSlot
  · rw [slot_frame h.fitS hf (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact h.roundsSlot
  · rw [hf.readW (r := ⟨K.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => (hd r hr).1.symm) (by decide)]
    exact h.key j hj
  · rw [hsy, hf.readW (r := ⟨(s.syms s1234Sym).setWidth 64, 4096⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => (hd r hr).2.1.symm) (by decide)]
    exact h.tab j hj q hq

/-- Round `i`'s precondition, with the subkeys' slot at `Kmᵢ`. -/
theorem Ctx.roundPre {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n) {i : Nat}
    (hi : 1 ≤ i ∧ i ≤ 16) (hkp : s.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (i - 1)))
    {l r : Spec.Cast5.Word} (hbx : s.gpr .ebx = l) (hbp : s.gpr .ebp = r) :
    RoundPre s S (K + BitVec.ofNat 32 (4 * (i - 1))) (k.getD (i - 1) 0) (k.getD (15 + i) 0) l r := by
  have hK := h.fitK
  have a0 : addr (K + BitVec.ofNat 32 (4 * (i - 1))) 0 = K.setWidth 64 + BitVec.ofNat 64 (4 * (i - 1)) := by
    have e := addr_eq (x := K) (k := 4 * (i - 1)) (by omega)
    unfold addr at e ⊢
    exact (congrArg (BitVec.setWidth 64) (BitVec.add_zero _)).trans e
  have a64 : addr (K + BitVec.ofNat 32 (4 * (i - 1))) 64 = K.setWidth 64 + BitVec.ofNat 64 (4 * (15 + i)) := by
    have e := addr_eq (x := K) (k := 4 * (15 + i)) (by omega)
    unfold addr at e ⊢
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 4 * (i - 1) + 64 = 4 * (15 + i) by omega]; exact e
  refine ⟨hbx, hbp, h.si, h.fitS, h.wS, hkp, ?_, ?_, ?_, ?_, h.sp, h.dS, h.fitT, h.inT, h.dT, h.tab⟩
  · rw [a0]; exact CallLay.inRegions_sub h.inK (by omega) (by decide)
  · rw [a0]; exact h.key _ (by omega)
  · rw [a64]; exact CallLay.inRegions_sub h.inK (by omega) (by decide)
  · rw [a64]; exact h.key _ (by omega)

/-- The state of a block's rounds, from `s`, with the halves `lr`. -/
structure RInv (s : State) (S K : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat)
    (lr : Spec.Cast5.Word × Spec.Cast5.Word) (u : State) : Prop where
  bx : u.gpr .ebx = lr.1
  bp : u.gpr .ebp = lr.2
  ctx : Ctx u S K k n
  same : ∀ q, q ∉ roundRegs → u.gpr q = s.gpr q
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  frame : Frame (blockMem S (s.gpr .esp)) s.mem u.mem

theorem roundMem_sub (S sp : BitVec 32) : ∀ r ∈ roundMem S sp, r ∈ blockMem S sp ∨
    Region.Sub r (slotR S kpOff 8) := by
  intro r hr
  simp only [roundMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (by simp [blockMem])
  · exact .inl (by simp [blockMem])
  · exact .inr (Offset.sub _ (by decide) (by decide))

/-- A frame of the round's regions is one of the block's. -/
theorem roundMem_frame {S sp : BitVec 32} {m m' : Mem} (h : Frame (roundMem S sp) m m') :
    Frame (blockMem S sp) m m' :=
  h.sub fun r hr => by
    rcases roundMem_sub S sp r hr with h' | h'
    · exact ⟨r, h', fun _ x => x⟩
    · exact ⟨_, by simp [blockMem], h'⟩

theorem round_step {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s S K k n lr u) {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3)
    (hi : 1 ≤ i ∧ i ≤ 16) (hkp : u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (i - 1))) (up : Bool) :
    WP isa (round t up) u fun v => RInv s S K k n (Spec.Cast5.round k i lr) v ∧
      v.mem.readW (addr S kpOff) 32 =
        (if up then K + BitVec.ofNat 32 (4 * (i - 1)) + 4 else K + BitVec.ofNat 32 (4 * (i - 1)) - 4) ∧
      v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 := by
  refine WP.mono (round_ok u ht up (h.ctx.roundPre hi hkp h.bx h.bp))
    fun v ⟨vbx, vbp, vkp, vf, vrd, vwr, vsy, vk⟩ => ?_
  have g (q : Reg) (hq : q ∉ roundRegs) : v.gpr q = u.gpr q := vk.gpr q hq
  have usp : u.gpr .esp = s.gpr .esp := h.same .esp (by decide)
  have vf' := roundMem_frame vf
  refine ⟨⟨vbx, ?_, h.ctx.transfer ((g .esi (by decide)).trans h.ctx.si) (g .esp (by decide)) vrd vwr vsy vf'
      (blockMem_disjoint h.ctx), fun q hq => (g q hq).trans (h.same q hq), vrd.trans h.rd, vwr.trans h.wr,
      vsy.trans h.syms, h.frame.trans (by rw [← usp]; exact vf')⟩, vkp, ?_⟩
  · rw [vbp, fT_eq ht hti]
    rfl
  · rw [addr_off h.ctx.fitS gcOff (by decide)]
    refine vf.readW (r := slotR S gcOff 4) (Offset.contains _ (by decide) (by decide) (by decide)) ?_ (by decide)
    intro r hr
    simp only [roundMem, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.ctx.dS.sub_left (slot_sub S (by decide)))
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- A slot's word, after a store to another slot. -/
theorem rd_sep {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 256) (he : e + 4 ≤ 256) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr S e) v).readW (addr S d) 32 = m.readW (addr S d) 32 :=
  Mem.readW_writeW_sep (w := 32) (w' := 32) (slot_sep hfit (by omega) (by omega) h (by decide) (by decide))
    (by decide)

theorem RInv.init {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (hbx : s.gpr .ebx = lr.1) (hbp : s.gpr .ebp = lr.2) :
    RInv s S K k n lr s :=
  ⟨hbx, hbp, h, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The state of the rounds is kept by code that writes registers of a
round but `ebx` and `ebp`, and the slots `kpOff` and `gcOff`. -/
theorem RInv.mono {s u v : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr u)
    (hbx : v.gpr .ebx = u.gpr .ebx) (hbp : v.gpr .ebp = u.gpr .ebp) (hg : ∀ q, q ∉ roundRegs → v.gpr q = u.gpr q)
    (hrd : v.rd = u.rd) (hwr : v.wr = u.wr) (hsy : v.syms = u.syms) (hf : Frame [slotR S kpOff 8] u.mem v.mem) :
    RInv s S K k n lr v := by
  have hd : ∀ r ∈ [slotR S kpOff 8], r.Disjoint ⟨K.setWidth 64, 128⟩ ∧
      r.Disjoint ⟨(u.syms s1234Sym).setWidth 64, 4096⟩ ∧ r.Disjoint (slotR S 48 16) := fun r hr =>
    blockMem_disjoint h.ctx r (by rw [List.mem_singleton] at hr; subst hr; simp [blockMem])
  refine ⟨hbx.trans h.bx, hbp.trans h.bp, h.ctx.transfer ((hg .esi (by decide)).trans h.ctx.si)
    (hg .esp (by decide)) hrd hwr hsy hf hd, fun q hq => (hg q hq).trans (h.same q hq), hrd.trans h.rd,
    hwr.trans h.wr, hsy.trans h.syms, h.frame.trans (hf.mono ?_)⟩
  intro r hr; rw [List.mem_singleton] at hr; subst hr
  rw [← h.same .esp (by decide)]; simp [blockMem]

theorem kp_contains (S : BitVec 32) (hfit : S.toNat + 256 ≤ 2 ^ 32) {d : Nat} (h1 : kpOff ≤ d) (h2 : d + 4 ≤ 72) :
    Region.Contains (slotR S kpOff 8) (addr S d) (32 / 8) := by
  rw [addr_off hfit d (by omega)]; exact Offset.contains _ h1 (by simp only [kpOff] at h2 ⊢; omega) (by decide)

/-- The count of groups left, down by one. -/
theorem countDown_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr u) :
    WP isa (.block [.mov .edx (.mem (at_ .esi gcOff)), .alu .sub .edx (imm 1), .store (at_ .esi gcOff) .edx]) u
      fun v => RInv s S K k n lr v ∧ v.mem.readW (addr S kpOff) 32 = u.mem.readW (addr S kpOff) 32 ∧
        v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 - 1 ∧
        v.zf = some (u.mem.readW (addr S gcOff) 32 - 1 == 0) := by
  have c := h.ctx
  have rg := slot_rd (s := u) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  have wg := slot_wr (s := u) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  crun [c.si, rg, wg]
  refine ⟨h.mono (by simp only [gpr_setReg]; rfl) (by simp only [gpr_setReg]; rfl) (fun q hq => ?_) rfl rfl rfl
    (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ (kp_contains S c.fitS (by decide) (by decide))),
    rd_sep c.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32 _ _ _, rfl⟩
  have : q ≠ .edx := fun e => hq (by rw [e]; decide)
  simp only [gpr_arithFlags, gpr_setReg, this, ite_false]

theorem four32 : (4 : BitVec 32) = BitVec.ofNat 32 4 := rfl

theorem add_ofNat_add32 (K : BitVec 32) (a b : Nat) :
    K + BitVec.ofNat 32 a + BitVec.ofNat 32 b = K + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sub_ofNat32 (K : BitVec 32) {a b : Nat} (h : b ≤ a) :
    K + BitVec.ofNat 32 a - BitVec.ofNat 32 b = K + BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := K.isLt
  omega

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {g : Nat} (hg : 3 * g + 3 ≤ 16)
    (h : RInv s S K k n (encFold k (3 * g) lr) u)
    (hkp : u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * g)) :
    WP isa (group true) u fun v => RInv s S K k n (encFold k (3 * (g + 1)) lr) v ∧
      v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * (g + 1)) ∧
      v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 - 1 ∧
      v.zf = some (u.mem.readW (addr S gcOff) 32 - 1 == 0) := by
  unfold group
  simp only [ite_true]
  refine WP.seq (WP.mono (round_step h (t := 1) (i := 3 * g + 1) (by decide) (by omega) (by omega)
    (by rw [hkp]; congr 2 <;> omega) true) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  rw [ite_eq_left rfl, four32, add_ofNat_add32] at a₁
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega) (by omega)
    (by rw [a₁]; congr 2 <;> omega) true) fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  rw [ite_eq_left rfl, four32, add_ofNat_add32] at a₂
  refine WP.seq (WP.mono (round_step h₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega) (by omega)
    (by rw [a₂]; congr 2 <;> omega) true) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  rw [ite_eq_left rfl, four32, add_ofNat_add32] at a₃
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega, encFold_succ, encFold_succ, encFold_succ]
    exact h₄
  · rw [a₄, a₃]; congr 2 <;> omega

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {m : Nat} (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0)
    (h : RInv s S K k n (decFold k n m lr) u)
    (hkp : u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - m - 1))) :
    WP isa (group false) u fun v => RInv s S K k n (decFold k n (m + 3) lr) v ∧
      v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - m - 1)) - 12 ∧
      v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 - 1 ∧
      v.zf = some (u.mem.readW (addr S gcOff) 32 - 1 == 0) := by
  unfold group
  simp only [Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (round_step h (t := 3) (i := n - m) (by decide) (by omega) (by omega)
    hkp false) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  rw [ite_eq_right Bool.false_ne_true, four32, sub_ofNat32 _ (by omega)] at a₁
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := n - m - 1) (by decide) (by omega) (by omega)
    (by rw [a₁]; congr 2 <;> omega) false) fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  rw [ite_eq_right Bool.false_ne_true, four32, sub_ofNat32 _ (by omega)] at a₂
  refine WP.seq (WP.mono (round_step h₂ (t := 1) (i := n - m - 2) (by decide) (by omega) (by omega)
    (by rw [a₂]; congr 2 <;> omega) false) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  rw [ite_eq_right Bool.false_ne_true] at a₃
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega,
      show n - (m + 2) = n - m - 2 by omega]
    exact h₄
  · rw [a₄, a₃]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := K.isLt
    rw [show (4 : BitVec 32).toNat = 4 from rfl, show (12 : BitVec 32).toNat = 12 from rfl]
    omega

/-- The count of groups: `rounds / 4 + 1`, and ZF set iff `rounds` is 16. -/
theorem groups_eq {n : Nat} (hn : n = 12 ∨ n = 16) :
    BitVec.ofNat 32 n >>> 2 + 1 = BitVec.ofNat 32 (n / 4 + 1) ∧
      (BitVec.ofNat 32 n - BitVec.ofNat 32 16 == 0) = decide (n = 16) := by
  rcases hn with rfl | rfl <;> decide

/-- The subkeys' slot at `Km₁`, the count of groups, and ZF set iff there are
16 rounds. -/
theorem encStart_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr s) :
    WP isa (.block (([.mov .edx (.mem (at_ .esi schedOff)), .store (at_ .esi kpOff) .edx] : List Instr) ++
      groups)) s fun u => RInv s S K k n lr u ∧ u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * 0) ∧
        u.mem.readW (addr S gcOff) 32 = BitVec.ofNat 32 (n / 4 + 1) ∧ u.zf = some (decide (n = 16)) := by
  have c := h.ctx
  have e1 : (s.mem.writeW (addr S kpOff) K).readW (addr S roundsOff) 32 = BitVec.ofNat 32 n := by
    rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact c.roundsSlot
  have e2 : ∀ v : BitVec 32, ((s.mem.writeW (addr S kpOff) K).writeW (addr S gcOff) v).readW (addr S roundsOff) 32 =
      BitVec.ofNat 32 n := fun v => by
    rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact e1
  have rs := slot_rd (s := s) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  have rr := slot_rd (s := s) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  have wk := slot_wr (s := s) c.fitS c.wS (d := kpOff) (n := 4) (by decide)
  have wg := slot_wr (s := s) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  obtain ⟨g1, g2⟩ := groups_eq c.nv
  unfold groups
  crun [c.si, rs, rr, wk, wg, c.schedSlot, e1, e2, g1, g2]
  refine ⟨h.mono (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl)
    (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl) (fun q hq => ?_) rfl rfl rfl ?_, ?_, ?_⟩
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    have b : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg, a, b, ite_false]
  · exact Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _
      (kp_contains S c.fitS (by decide) (by decide))) List.mem_cons_self _ (kp_contains S c.fitS (by decide) (by decide))
  · rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    exact (BitVec.add_zero K).symm
  · rw [Mem.readW_writeW_self32]; exact g1

/-- `cmp rounds, 16`. -/
theorem cmp16_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr u) :
    WP isa (.block [.mov .ecx (.mem (at_ .esi roundsOff)), .alu .cmp .ecx (imm 16)]) u fun v =>
      RInv s S K k n lr v ∧ v.mem = u.mem ∧ v.zf = some (decide (n = 16)) := by
  have c := h.ctx
  have rr := slot_rd (s := u) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  crun [c.si, rr, c.roundsSlot, (groups_eq c.nv).2]
  refine h.mono (by simp only [gpr_arithFlags, gpr_setReg]; rfl) (by simp only [gpr_arithFlags, gpr_setReg]; rfl)
    (fun q hq => ?_) rfl rfl rfl (Frame.refl _ _)
  have b : q ≠ .ecx := fun e => hq (by rw [e]; decide)
  simp only [gpr_arithFlags, gpr_setReg, b, ite_false]

theorem encryptBlock_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (hbx : s.gpr .ebx = lr.1) (hbp : s.gpr .ebp = lr.2) :
    WP isa encryptBlock s fun v => RInv s S K k n (encFold k n lr) v := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 32 ∧ 3 * (n / 4) ≤ 12 := by rcases h.nv with rfl | rfl <;> decide
  unfold encryptBlock
  refine WP.seq (WP.mono (encStart_ok (RInv.init h hbx hbp)) fun u ⟨hu, ukp, ugc, _⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdownF (fun v => v.mem.readW (addr S gcOff) 32) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g v => RInv s S K k n (encFold k (3 * g) lr) v ∧ v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * g))
    (fun g hg v ⟨hv, hkp⟩ _ => WP.mono (groupEnc_ok (by omega) hv hkp) fun w ⟨hw, wkp, wgc, wz⟩ =>
      ⟨⟨hw, wkp⟩, wgc, wz⟩)
    (fun _ h => h) ⟨hu, ukp⟩ ugc) fun v ⟨hv, vkp⟩ => ?_)
  refine WP.seq (WP.mono (cmp16_ok hv) fun w ⟨hw, wm, wz⟩ => ?_)
  refine WP.ite (decide (n = 16)) wz (fun h16 => ?_) (fun h16 => ?_)
  · have hn : n = 16 := of_decide_eq_true h16
    refine WP.mono (round_step hw (t := 1) (i := 16) (by decide) (by decide) (by decide)
      (by rw [wm, vkp, hn]) true) fun x ⟨hx, _, _⟩ => ?_
    rw [hn, show 16 = 15 + 1 from rfl, encFold_succ]
    rw [hn] at hx
    exact hx
  · have hn : n = 12 := by
      rcases h.nv with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false h16)
    refine WP.block_nil ?_
    rw [hn] at hw ⊢
    exact hw

theorem decKp_eq (K : BitVec 32) {n : Nat} (hn : n = 12 ∨ n = 16) :
    BitVec.ofNat 32 n + BitVec.ofNat 32 n + (BitVec.ofNat 32 n + BitVec.ofNat 32 n) + K - 4#32 =
      K + BitVec.ofNat 32 (4 * (n - 1)) := by
  apply BitVec.eq_of_toNat_eq
  have := K.isLt
  rcases hn with rfl | rfl <;>
  · simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- The subkeys' slot at `Kmₙ`, the count of groups, and ZF set iff there
are 16 rounds. -/
theorem decStart_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr s) :
    WP isa (.block (([.mov .edx (.mem (at_ .esi roundsOff)), .alu .add .edx (.reg .edx),
      .alu .add .edx (.reg .edx), .mov .ecx (.mem (at_ .esi schedOff)), .alu .add .edx (.reg .ecx),
      .alu .sub .edx (imm 4),
      .store (at_ .esi kpOff) .edx] : List Instr) ++ groups)) s fun u =>
      RInv s S K k n lr u ∧ u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - 1)) ∧
        u.mem.readW (addr S gcOff) 32 = BitVec.ofNat 32 (n / 4 + 1) ∧ u.zf = some (decide (n = 16)) := by
  have c := h.ctx
  have e1 : ∀ v : BitVec 32, (s.mem.writeW (addr S kpOff) v).readW (addr S roundsOff) 32 = BitVec.ofNat 32 n :=
    fun v => by rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact c.roundsSlot
  have e2 : ∀ v w : BitVec 32, ((s.mem.writeW (addr S kpOff) v).writeW (addr S gcOff) w).readW (addr S roundsOff) 32 =
      BitVec.ofNat 32 n := fun v w => by
    rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact e1 v
  have rs := slot_rd (s := s) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  have rr := slot_rd (s := s) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  have wk := slot_wr (s := s) c.fitS c.wS (d := kpOff) (n := 4) (by decide)
  have wg := slot_wr (s := s) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  obtain ⟨g1, g2⟩ := groups_eq c.nv
  unfold groups
  crun [c.si, rs, rr, wk, wg, c.schedSlot, c.roundsSlot, e1, e2, g1, g2, decKp_eq K c.nv]
  refine ⟨h.mono (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl)
    (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl) (fun q hq => ?_) rfl rfl rfl ?_, ?_, ?_⟩
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    have b : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg, a, b, ite_false]
  · exact Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _
      (kp_contains S c.fitS (by decide) (by decide))) List.mem_cons_self _ (kp_contains S c.fitS (by decide) (by decide))
  · rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]; exact g1

theorem decFold_zero (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    decFold k n 0 lr = lr := rfl

theorem decryptBlock_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (hbx : s.gpr .ebx = lr.1) (hbp : s.gpr .ebp = lr.2) :
    WP isa decryptBlock s fun v => RInv s S K k n (decFold k n n lr) v := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 32 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases h.nv with rfl | rfl <;> decide
  unfold decryptBlock
  refine WP.seq (WP.mono (decStart_ok (RInv.init h hbx hbp)) fun u ⟨hu, ukp, ugc, uz⟩ => ?_)
  -- Round 16 first, if there are 16.
  have first : WP isa (.ite .e (round 1 false) (.block [])) u fun v =>
      RInv s S K k n (decFold k n (n % 3) lr) v ∧
        v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - n % 3 - 1)) ∧
        v.mem.readW (addr S gcOff) 32 = BitVec.ofNat 32 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) uz (fun h16 => ?_) (fun h16 => ?_)
    · have hn : n = 16 := of_decide_eq_true h16
      refine WP.mono (round_step hu (t := 1) (i := n) (by decide) (by rw [hn]) (by omega) ukp false)
        fun x ⟨hx, xkp, xgc⟩ => ?_
      have hd : decFold k n (n % 3) lr = Spec.Cast5.round k n lr := by
        rw [hn, show 16 % 3 = 0 + 1 from rfl, decFold_succ, decFold_zero, Nat.sub_zero]
      refine ⟨(by rw [hd]; exact hx), ?_, xgc.trans ugc⟩
      rw [xkp, ite_eq_right Bool.false_ne_true, four32, sub_ofNat32 _ (by omega)]
      congr 2; omega
    · have hn : n = 12 := by
        rcases h.nv with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false h16)
      have hd : decFold k n (n % 3) lr = lr := by rw [hn, show 12 % 3 = 0 from rfl, decFold_zero]
      refine WP.block_nil ⟨(by rw [hd]; exact hu), ?_, ugc⟩
      rw [ukp, hn]
  refine WP.seq (WP.mono first fun v ⟨hv, vkp, vgc⟩ => ?_)
  -- Then the groups of three.
  refine wp_countdownF (fun w => w.mem.readW (addr S gcOff) 32) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => RInv s S K k n (decFold k n (n % 3 + 3 * g) lr) w ∧
      (n % 3 + 3 * g < n → w.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, wkp⟩ _ => WP.mono (groupDec_ok (m := n % 3 + 3 * g) (by omega) (by
        rcases h.nv with rfl | rfl <;> decide) (by omega) hw (wkp (by omega)))
      fun x ⟨hx, xkp, xgc, xz⟩ =>
        ⟨⟨(show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega) ▸ hx, fun hlt => ?_⟩, xgc, xz⟩)
    (fun w ⟨hw, _⟩ => by rw [hG.2.2.1] at hw; exact hw)
    ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact vkp⟩ vgc
  rw [xkp, show (12 : BitVec 32) = BitVec.ofNat 32 12 from rfl, sub_ofNat32 _ (by omega)]
  congr 2
  omega

/-! ## A block at the data slot -/

theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, show 32 / 8 = 4 from rfl]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

/-- The 8 bytes of the block at `D`. -/
abbrev blockR (D : BitVec 32) : Region := ⟨D.setWidth 64, 8⟩

/-- What `crypt` needs: the context, and the block at `D`, the address in
the data slot, apart from the working space, the subkeys, the table and the
word below `esp`. -/
structure BPre (s : State) (S K D : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  ctx : Ctx s S K k n
  dataSlot : s.mem.readW (addr S dataOff) 32 = D
  fitD : D.toNat + 8 ≤ 2 ^ 32
  wD : InRegions s.wr (D.setWidth 64) 8
  dDS : Region.Disjoint (blockR D) ⟨S.setWidth 64, 256⟩
  dDK : Region.Disjoint (blockR D) ⟨K.setWidth 64, 128⟩
  dDT : Region.Disjoint (blockR D) ⟨(s.syms s1234Sym).setWidth 64, 4096⟩
  dDsp : Region.Disjoint (blockR D) (below (s.gpr .esp) 4)

/-- Encryption or decryption of a block. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : Spec.Cast5.Block) : Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n b else Spec.Cast5.decryptBlock k n b

/-- The rounds of `cipher`. -/
def fold (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    Spec.Cast5.Word × Spec.Cast5.Word :=
  if up then encFold k n lr else decFold k n n lr

theorem cipher_eq (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : Spec.Cast5.Block) :
    cipher up k n b = Spec.Cast5.encodeBlock ((fold up k n (Spec.Cast5.decodeBlock b)).2,
      (fold up k n (Spec.Cast5.decodeBlock b)).1) := by
  cases up
  · exact decryptBlock_eq k n b
  · exact encryptBlock_eq k n b

theorem addr_D0 {D : BitVec 32} (h : D.toNat + 8 ≤ 2 ^ 32) : addr D 0 = D.setWidth 64 := by
  rw [addr_off h 0 (by decide), BitVec.add_zero]

theorem load_ok {s : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s S K D k n) :
    WP isa (.block load) s fun u => Ctx u S K k n ∧
      (u.gpr .ebx, u.gpr .ebp) = Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (D.setWidth 64)) ∧
      u.mem = s.mem ∧ (∀ q, q ∉ roundRegs → u.gpr q = s.gpr q) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have c := h.ctx
  have rd := slot_rd (s := s) c.fitS c.wS (d := dataOff) (n := 4) (by decide)
  have r0 : InRegions (s.rd ++ s.wr) (addr D 0) 4 := by
    rw [addr_D0 h.fitD]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact (CallLay.inRegions_sub (off := 0) (l := 4) ⟨g, List.mem_append_right _ hg, hc⟩ (by omega) (by decide)).imp
      fun _ ⟨a, b⟩ => ⟨a, by rwa [BitVec.add_zero] at b⟩
  have r4 : InRegions (s.rd ++ s.wr) (addr D 4) 4 := by
    rw [addr_off h.fitD 4 (by decide)]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega) (by decide)
  unfold load
  crun [c.si, rd, h.dataSlot, r0, r4]
  refine ⟨c.transfer (by simp only [gpr_setReg]; exact c.si) rfl rfl rfl rfl (Frame.refl [] _) (by simp), ?_,
    fun q hq => ?_⟩
  · rw [decodeBlock_blockAt, addr_D0 h.fitD, addr_off h.fitD 4 (by decide)]
    rfl
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    have b : q ≠ .ebx := fun e => hq (by rw [e]; decide)
    have d : q ≠ .ebp := fun e => hq (by rw [e]; decide)
    simp only [a, b, d, ite_false]

/-- What `crypt` does. -/
structure BPost (s : State) (S D : BitVec 32) (out : Spec.Cast5.Block) (v : State) : Prop where
  blk : Spec.Cast5.blockAt v.mem (D.setWidth 64) = out
  frame : Frame (blockR D :: blockMem S (s.gpr .esp)) s.mem v.mem
  same : ∀ q, q ∉ roundRegs → v.gpr q = s.gpr q
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  syms : v.syms = s.syms

/-- A slot of `48 … 63` through the writes of a block. -/
theorem slot_block {m : Mem} {S D : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (hD : D.toNat + 8 ≤ 2 ^ 32)
    (hd : Region.Disjoint (blockR D) ⟨S.setWidth 64, 256⟩) (x y : BitVec 32) {e : Nat} (h1 : 48 ≤ e)
    (h2 : e + 4 ≤ 64) :
    ((m.writeW (addr D 0) x).writeW (addr D 4) y).readW (addr S e) 32 = m.readW (addr S e) 32 := by
  have hs (o : Nat) (ho : o + 4 ≤ 8) : Mem.Sep (addr S e) 4 (addr D o) 4 := by
    refine Region.Disjoint.sep hd.symm ?_ ?_
    · rw [addr_off hfit e (by omega)]; exact Offset.contains_base _ (by omega) (by omega)
    · rw [addr_off hD o (by omega)]; exact Offset.contains_base _ (by omega) (by omega)
  rw [Mem.readW_writeW_sep (w' := 32) (hs 4 (by decide)) (by decide),
    Mem.readW_writeW_sep (w' := 32) (hs 0 (by decide)) (by decide)]

theorem store_ok {s u : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : BPre s S K D k n) (hu : RInv s S K k n lr u) :
    WP isa (.block store) u (BPost s S D (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have c := hu.ctx
  have usp : u.gpr .esp = s.gpr .esp := hu.same .esp (by decide)
  have uD : u.mem.readW (addr S dataOff) 32 = D := by
    rw [slot_frame c.fitS hu.frame (fun r hr => (blockMem_disjoint h.ctx r hr).2.2) (by decide) (by decide)]
    exact h.dataSlot
  obtain ⟨N, hN⟩ : ∃ N, u.mem.readW (addr S nOff) 32 = N := ⟨_, rfl⟩
  have w0 : InRegions u.wr (addr D 0) 4 := by
    rw [addr_D0 h.fitD, hu.wr]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact ⟨g, hg, by unfold Region.Contains at hc ⊢; omega⟩
  have w4 : InRegions u.wr (addr D 4) 4 := by
    rw [addr_off h.fitD 4 (by decide), hu.wr]
    exact CallLay.inRegions_sub h.wD (by omega) (by decide)
  have rdD := slot_rd (s := u) c.fitS c.wS (d := dataOff) (n := 4) (by decide)
  have rsS := slot_rd (s := u) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  have rrR := slot_rd (s := u) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  have rnN := slot_rd (s := u) c.fitS c.wS (d := nOff) (n := 4) (by decide)
  have wdD := slot_wr (s := u) c.fitS c.wS (d := dataOff) (n := 4) (by decide)
  have wsS := slot_wr (s := u) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  have wrR := slot_wr (s := u) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  have wnN := slot_wr (s := u) c.fitS c.wS (d := nOff) (n := 4) (by decide)
  have hbx := hu.bx
  have hbp := hu.bp
  -- The block written, then the public slots written back with what they hold.
  obtain ⟨m', hm'⟩ : ∃ m', (u.mem.writeW (addr D 0) (byteRev32 lr.2)).writeW (addr D 4) (byteRev32 lr.1) = m' :=
    ⟨_, rfl⟩
  have sb (e : Nat) (h1 : 48 ≤ e) (h2 : e + 4 ≤ 64) : m'.readW (addr S e) 32 = u.mem.readW (addr S e) 32 := by
    rw [← hm']; exact slot_block c.fitS h.fitD (h.dDS) _ _ h1 h2
  have e : (((m'.writeW (addr S dataOff) D).writeW (addr S schedOff) K).writeW (addr S roundsOff)
      (BitVec.ofNat 32 n)).writeW (addr S nOff) N = m' := by
    rw [← uD, ← sb dataOff (by decide) (by decide), writeW_readW, ← c.schedSlot, ← sb schedOff (by decide) (by decide),
      writeW_readW, ← c.roundsSlot, ← sb roundsOff (by decide) (by decide), writeW_readW, ← hN,
      ← sb nOff (by decide) (by decide), writeW_readW]
  unfold store
  crun [c.si, rdD, rsS, rrR, rnN, uD, c.schedSlot, c.roundsSlot, hN, w0, w4, wdD, wsS, wrR, wnN, hbx, hbp,
    bswap_eq, hm', e]
  refine ⟨?_, ?_, fun q hq => ?_, hu.rd, hu.wr, hu.syms⟩
  · rw [← hm', addr_D0 h.fitD, addr_off h.fitD 4 (by decide), blockAt_write]
  · rw [← hm']
    have c0 : (blockR D).Contains (addr D 0) (32 / 8) := by
      rw [addr_D0 h.fitD]; simp [Region.Contains]
    have c4 : (blockR D).Contains (addr D 4) (32 / 8) := by
      rw [addr_off h.fitD 4 (by decide)]; exact Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by decide) (by decide)
    have f1 := (hu.frame.mono (rs' := blockR D :: blockMem S (s.gpr .esp))
      (fun r hr => List.mem_cons_of_mem _ hr)).writeW List.mem_cons_self (byteRev32 lr.2) c0
    exact f1.writeW List.mem_cons_self (byteRev32 lr.1) c4
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    have b : q ≠ .eax := fun e => hq (by rw [e]; decide)
    have d : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    have f : q ≠ .edi := fun e => hq (by rw [e]; decide)
    have g : q ≠ .ebx := fun e => hq (by rw [e]; decide)
    have i : q ≠ .ebp := fun e => hq (by rw [e]; decide)
    simp only [gpr_setReg, a, b, d, f, g, i, ite_false]
    exact hu.same q hq

theorem crypt_ok {s : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s S K D k n)
    (up : Bool) :
    WP isa (crypt up) s (BPost s S D (cipher up k n (Spec.Cast5.blockAt s.mem (D.setWidth 64)))) := by
  unfold crypt
  refine WP.seq (WP.mono (load_ok h) fun u ⟨hu, hlr, um, ug, urd, uwr, usy⟩ => ?_)
  have usp : u.gpr .esp = s.gpr .esp := ug .esp (by decide)
  have hb : BPre u S K D k n := ⟨hu, by rw [um]; exact h.dataSlot, h.fitD, by rw [uwr]; exact h.wD, h.dDS, h.dDK,
    by rw [usy]; exact h.dDT, by rw [usp]; exact h.dDsp⟩
  obtain ⟨lr, hlr'⟩ : ∃ lr, Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (D.setWidth 64)) = lr := ⟨_, rfl⟩
  rw [hlr'] at hlr
  have hbx : u.gpr .ebx = lr.1 := by rw [← hlr]
  have hbp : u.gpr .ebp = lr.2 := by rw [← hlr]
  have post (v : State) (hv : RInv u S K k n (fold up k n lr) v) :
      WP isa (.block store) v (BPost s S D (cipher up k n (Spec.Cast5.blockAt s.mem (D.setWidth 64)))) := by
    refine WP.mono (store_ok hb hv) fun w hw => ?_
    rw [cipher_eq, hlr']
    exact ⟨hw.blk, by rw [← um, ← usp]; exact hw.frame, fun q hq => (hw.same q hq).trans (ug q hq),
      hw.rd.trans urd, hw.wr.trans uwr, hw.syms.trans usy⟩
  cases up
  · exact WP.seq (WP.mono (decryptBlock_ok hu hbx hbp) fun v hv => post v hv)
  · exact WP.seq (WP.mono (encryptBlock_ok hu hbx hbp) fun v hv => post v hv)

end VG.Proof.Cast5.X86
