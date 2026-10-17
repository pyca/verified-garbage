module

public import VerifiedGarbage.Proof.MdStream.X86_64.Common
public import VerifiedGarbage.Proof.MdStream.OneShot
public import VerifiedGarbage.Impl.MdStream.X86_64.OneShot
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# One-shot Merkle–Damgård digests on x86-64

The functional correctness of `OneShot.body` (`Impl/MdStream/X86_64/OneShot.lean`),
the one-shot digest given its scratch buffer, for any hash function (`Md`),
any correct compression function (`CalleeOk`), any code `init` storing an
initial hash value `iv` (writing only `rax`), and the hash function's length
field and digest code (`ShapeD`): it runs `init`, compresses the whole blocks
of the message, builds the last block or two in the buffer (as `Md.hash_one`
and `Md.hash_two` describe them) and compresses them, and writes the digest.
The compression function is called as the streaming code calls it
(`compressWith_ok`).
-/

@[expose] public section

namespace VG.Proof.MdStream.X86_64.OneShot

open VG VG.X86_64 VG.Impl.MdStream.X86_64 VG.Impl.MdStream.X86_64.OneShot
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.OneShot (itp itn getD_congr writeW128_off writeW8_off writeBytes_off readW128_byte
  pad1_getD pad2a_getD pad2b_getD)

/-! ## The precondition -/

section
variable (P : Params) (s : State)

abbrev dp : Addr := s.gpr .rdi
abbrev len : Nat := (s.gpr .rsi).toNat
abbrev out : Addr := s.gpr .rdx
/-- The scratch buffer. -/
abbrev sb : Addr := s.gpr .rcx
abbrev dR : Region := ⟨dp s, len s⟩
abbrev oR (D : Nat) : Region := ⟨out s, D⟩
abbrev wR : Region := ⟨sb s, scratchBytes P⟩
/-- The hash value, the block, the compression function's scratch space and
the saved registers, in the buffer. -/
abbrev hR : Region := ⟨sb s, P.N⟩
abbrev bR : Region := ⟨sb s + BitVec.ofNat 64 P.N, P.B⟩
abbrev scR : Region := ⟨sb s + BitVec.ofNat 64 (scO P), P.so⟩
abbrev slR : Region := ⟨sb s + BitVec.ofNat 64 (scO P + P.so), 48⟩
/-- Where the calls store their return addresses. -/
abbrev stkR : Region := below (s.gpr .rsp) 8
abbrev retR : Region := ⟨s.gpr .rsp, 8⟩

end

/-- The message is readable, `out` and the scratch buffer writable, and none
of them overlaps another, the return address or the 8 bytes below it. -/
structure Pre (P : Params) (D : Nat) (s : State) : Prop where
  rd : s.rd = [dR s]
  wr : s.wr = [oR s D, wR P s]
  d_o : (dR s).Disjoint (oR s D)
  d_w : (dR s).Disjoint (wR P s)
  o_w : (oR s D).Disjoint (wR P s)
  ret_o : (retR s).Disjoint (oR s D)
  ret_w : (retR s).Disjoint (wR P s)
  stk_d : (stkR s).Disjoint (dR s)
  stk_o : (stkR s).Disjoint (oR s D)
  stk_w : (stkR s).Disjoint (wR P s)

/-- The contract of the body: the first `D` bytes of the digest, from `iv`, of
the message. -/
def oneK {P : Params} (H : Md P.B P.N P.L) (iv : H.HV) (D : Nat) : Contract isa where
  pre := Pre P D
  post s s' := H.lenOk (len s) →
    bytesAt s'.mem (out s) D = (H.hash iv (bytesAt s.mem (dp s) (len s))).take D
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- What the code storing the initial hash value does: on a state whose only
region is the streaming state at `rdi`, it makes the state represent the
empty message. -/
def initK {P : Params} (H : Md P.B P.N P.L) (iv : H.HV) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, P.N + P.B⟩] ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, P.N + P.B⟩
  post s s' := H.Repr iv s'.mem (s.gpr .rdi) []
  pub _ _ := True

/-- The buffer fits a frame of less than a page. -/
structure Fits (P : Params) : Prop where
  lt : scratchBytes P < 4096

/-! ## The buffer -/

section
variable {P : Params}

theorem st_le (P : Params) : P.N + P.B ≤ scO P := by simp only [scO]; omega

theorem sc_le (P : Params) : scO P + P.so + 48 = scratchBytes P := rfl

variable (hF : Fits P) (s : State)
include hF

theorem h_b : (hR P s).Disjoint (bR P s) :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hF.lt; have := st_le P; have := sc_le P; omega)

theorem h_sc : (hR P s).Disjoint (scR P s) :=
  Offset.base_disjoint _ (by have := st_le P; omega) (by have := hF.lt; have := sc_le P; omega)

theorem b_sc : (bR P s).Disjoint (scR P s) :=
  Offset.disjoint _ (.inl (st_le P)) (by have := hF.lt; have := st_le P; have := sc_le P; omega)
    (by have := hF.lt; have := sc_le P; omega)

theorem h_sl : (hR P s).Disjoint (slR P s) :=
  Offset.base_disjoint _ (by have := st_le P; omega) (by have := hF.lt; have := sc_le P; omega)

theorem b_sl : (bR P s).Disjoint (slR P s) :=
  Offset.disjoint _ (.inl (by have := st_le P; omega)) (by have := hF.lt; have := st_le P; have := sc_le P; omega)
    (by have := hF.lt; have := sc_le P; omega)

theorem sc_sl : (scR P s).Disjoint (slR P s) :=
  Offset.disjoint _ (.inl (Nat.le_refl _)) (by have := hF.lt; have := sc_le P; omega)
    (by have := hF.lt; have := sc_le P; omega)

end

section
variable {P : Params} (s : State)

theorem h_sub : Region.Sub (hR P s) (wR P s) :=
  Region.sub_prefix (by have := st_le P; have := sc_le P; omega)

theorem b_sub : Region.Sub (bR P s) (wR P s) :=
  Offset.sub_base _ (by have := st_le P; have := sc_le P; omega)

theorem sc_sub : Region.Sub (scR P s) (wR P s) :=
  Offset.sub_base _ (by have := sc_le P; omega)

theorem sl_sub : Region.Sub (slR P s) (wR P s) :=
  Offset.sub_base _ (by rw [← sc_le P])

end

/-! ## The saved registers -/

/-- The callee-saved registers of `s`, at `slO`. -/
def Slots (P : Params) (s : State) (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (p.2 : Int)) 64 = s.gpr p.1

theorem slot_eq {P : Params} (s : State) {d : Nat} :
    sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (d : Int) = sb s + BitVec.ofNat 64 (scO P + d) := by
  rw [ofInt_natCast, add_ofNat]

theorem slot_contains {P : Params} (hd : Dims P) (s : State) {p : Reg × Nat} (hp : p ∈ saved P) :
    (slR P s).Contains (sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (p.2 : Int)) 8 := by
  have := saved_offset hd hp
  rw [slot_eq, show scO P + p.2 = scO P + P.so + (p.2 - P.so) by omega, ← add_ofNat]
  exact Offset.contains_base _ (by omega) (by omega)

/-! ## Between the phases -/

/-- What every state of the body keeps of `s`, the state on entry. -/
structure Mid (P : Params) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  rsp : t.gpr .rsp = s.gpr .rsp
  rbx : t.gpr .rbx = sb s
  r15 : t.gpr .r15 = sb s + BitVec.ofNat 64 (scO P)
  rbp : t.gpr .rbp = out s
  r12 : t.gpr .r12 = s.gpr .rsi
  frame : Frame [wR P s, stkR s] s.mem t.mem
  slots : Slots P s t.mem

/-- The registers `Mid` keeps. -/
abbrev midRegs : List Reg := [.rsp, .rbx, .r15, .rbp, .r12]

/-- The registers our code writes, besides the compression function's. -/
def scratchRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r13, .r14]

theorem mid_ne : ∀ r ∈ midRegs, ∀ q ∈ scratchRegs, r ≠ q := by decide

theorem mid_cs : ∀ r ∈ midRegs, r ∈ calleeSaved := by decide

/-- A change of memory within regions of the buffer other than the saved
registers', and of no register `Mid` keeps, keeps `Mid`. -/
theorem Mid.of_frame {P : Params} (hd : Dims P) {s t t' : State} (h : Mid P s t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ midRegs, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ [wR P s, stkR s], Region.Sub r r')
    (hsl : ∀ r ∈ rs, (slR P s).Disjoint r) : Mid P s t' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rsp := (hg _ (by simp)).trans h.rsp
  rbx := (hg _ (by simp)).trans h.rbx
  r15 := (hg _ (by simp)).trans h.r15
  rbp := (hg _ (by simp)).trans h.rbp
  r12 := (hg _ (by simp)).trans h.r12
  frame := h.frame.trans (hf.sub hsub)
  slots p hp := by
    rw [← h.slots p hp]
    exact hf.readW (slot_contains hd s hp) hsl (by decide)

/-- `Mid` through code that changes no memory. -/
theorem Mid.of_regs {P : Params} (hd : Dims P) {s t t' : State} (h : Mid P s t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ midRegs, t'.gpr r = t.gpr r) : Mid P s t' :=
  Mid.of_frame hd h hrd hwr hg (rs := []) (fun x _ => by rw [hm]) (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)

/-- `Mid` through stores to the block. -/
theorem Mid.of_blk {P : Params} (hF : Fits P) (hd : Dims P) {s t t' : State} (h : Mid P s t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ midRegs, t'.gpr r = t.gpr r)
    (hf : Frame [bR P s] t.mem t'.mem) : Mid P s t' :=
  Mid.of_frame hd h hrd hwr hg hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., b_sub s⟩)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (b_sl hF s).symm)

/-- The message. -/
abbrev msg (s : State) : List Byte := bytesAt s.mem (dp s) (len s)

theorem msg_length (s : State) : (msg s).length = len s := by simp [bytesAt]

theorem msg_getD (s : State) {i : Nat} (hi : i < len s) : (msg s).getD i 0 = s.mem (dp s + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem len_lt (s : State) : len s < 2 ^ 64 := (s.gpr .rsi).isLt

theorem rsi_eq (s : State) : s.gpr .rsi = BitVec.ofNat 64 (len s) := by simp [len]

/-- The message's bytes are those on entry: the buffer and the stack are
disjoint from it. -/
theorem data_eq {P : Params} {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t) {i : Nat}
    (hi : i < len s) : t.mem (dp s + BitVec.ofNat 64 i) = (msg s).getD i 0 := by
  rw [msg_getD s hi]
  exact h.frame.bytes (R := dR s)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_w
      · exact hp.stk_d.symm)
    (Nat.le_of_lt (len_lt s)) hi

/-! ## `setup`: saving our caller's registers -/

theorem sx_lt {n : Nat} (h : n < 4096) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n :=
  sx_ofNat (by omega)

theorem setup_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s : State} (hp : Pre P D s) :
    WP isa (.block (setup P)) s fun t => Mid P s t ∧ t.gpr .r13 = dp s ∧ t.gpr .rdi = sb s := by
  have hlt := hF.lt; have := st_le P; have := sc_le P; have := hd.so
  unfold setup
  refine wp_addi fun s₁ u₁ => ?_
  have h1 : s₁.gpr .rcx = sb s + BitVec.ofNat 64 (scO P) := by rw [u₁.gpr, sx_lt (by omega)]
  have hin : ∀ {t : State}, t.wr = s.wr → ∀ p ∈ saved P,
      InRegions t.wr (s₁.gpr .rcx + BitVec.ofInt 64 (p.2 : Int)) 8 := fun hw p hq => by
    have := saved_offset hd hq
    refine ⟨wR P s, by rw [hw, hp.wr]; simp, ?_⟩
    rw [h1, slot_eq]; exact Offset.contains_base _ (by omega) (by omega)
  have w₁ : s₁.wr = s.wr := u₁.wr
  rw [save_eq]
  refine wp_store (a := s₁.gpr .rcx + BitVec.ofInt 64 ((P.so : Nat) : Int)) rfl
    (hin w₁ (.rbx, P.so) (by simp [saved])) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := s₁.gpr .rcx + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (by rw [ea_at, g₂])
    (hin (wr₂.trans w₁) (.rbp, P.so + 8) (by simp [saved])) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := s₁.gpr .rcx + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int)) (by rw [ea_at, g₃, g₂])
    (hin (wr₃.trans (wr₂.trans w₁)) (.r12, P.so + 16) (by simp [saved])) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := s₁.gpr .rcx + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int)) (by rw [ea_at, g₄, g₃, g₂])
    (hin (wr₄.trans (wr₃.trans (wr₂.trans w₁))) (.r13, P.so + 24) (by simp [saved])) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := s₁.gpr .rcx + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int)) (by rw [ea_at, g₅, g₄, g₃, g₂])
    (hin (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans w₁)))) (.r14, P.so + 32) (by simp [saved]))
    fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  refine wp_store (a := s₁.gpr .rcx + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int))
    (by rw [ea_at, g₆, g₅, g₄, g₃, g₂])
    (hin (wr₆.trans (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans w₁))))) (.r15, P.so + 40) (by simp [saved]))
    fun s₇ g₇ m₇ rd₇ wr₇ => ?_
  have g : s₇.gpr = s₁.gpr := by rw [g₇, g₆, g₅, g₄, g₃, g₂]
  have hm : s₇.mem = saveMem P s₁ .rcx := by
    rw [m₇, m₆, m₅, m₄, m₃, m₂, g₆, g₅, g₄, g₃, g₂]; rfl
  refine wp_mov fun s₈ u₈ _ _ => wp_mov fun s₉ u₉ _ _ => wp_subi fun s₁₀ u₁₀ _ =>
    wp_mov fun s₁₁ u₁₁ _ _ => wp_mov fun s₁₂ u₁₂ _ _ => wp_mov fun s₁₃ u₁₃ _ _ =>
    wp_mov fun s₁₄ u₁₄ _ _ => WP.block_nil ?_
  -- Every register but those written is that of `s₇`, so of `s₁`.
  have k : ∀ r, r ≠ .rdi → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .rbx → r ≠ .r15 →
      s₁₄.gpr r = s₇.gpr r := fun r h0 h1 h2 h3 h4 h5 => by
    rw [u₁₄.other _ h0, u₁₃.other _ h1, u₁₂.other _ h2, u₁₁.other _ h3, u₁₀.other _ h4, u₉.other _ h4,
      u₈.other _ h5]
  have e : ∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r := fun r hr => u₁.other r hr
  have hrbx₁₃ : s₁₃.gpr .rbx = sb s := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), g, h1, sx_lt (by omega), BitVec.add_sub_cancel]
  have hrbx : s₁₄.gpr .rbx = sb s := (u₁₄.other _ (by decide)).trans hrbx₁₃
  have hmem : s₁₄.mem = s₇.mem := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
  refine ⟨⟨?_, ?_, ?_, hrbx, ?_, ?_, ?_, ?_, fun p hp => ?_⟩, ?_, ?_⟩
  · rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, u₁.rd]
  · rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, w₁]
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g, e _ (by decide)]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, g, h1]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), g, e _ (by decide)]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), g, e _ (by decide)]
  · rw [hmem, hm, ← u₁.mem]
    exact (saveMem_frame hd).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wR P s, List.mem_cons_self .., by rw [h1]; exact Offset.sub_base _ (by omega)⟩
  · have hne : p.1 ≠ .rcx := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    have := saveMem_saved (P := P) (s₀ := s₁) (b := .rcx) hd p hp
    rw [h1, e _ hne] at this
    rw [hmem, hm, this]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), g, e _ (by decide)]
  · rw [u₁₄.gpr, hrbx₁₃]

/-! ## `init` -/

/-- Regions at offsets within the buffer are covered by the writable regions. -/
theorem covers_w {P : Params} {D : Nat} {s : State} (hp : Pre P D s) {t : State} (hwr : t.wr = s.wr)
    {rs : List Region} (h : ∀ r ∈ rs, ∃ off, r.base = sb s + BitVec.ofNat 64 off ∧ off + r.len ≤ scratchBytes P) :
    Covers rs t.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨wR P s, by rw [hwr, hp.wr]; simp, off, hb, hl⟩

theorem sb_zero (s : State) : sb s = sb s + BitVec.ofNat 64 0 := by simp

theorem init_ok {P : Params} (hF : Fits P) (hd : Dims P) {H : Md P.B P.N P.L} {iv : H.HV} {init : Prog isa}
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .rax → ∀ i ∈ instrs init, Taint.clobbers i r = false) (hin : init.noCalls = true)
    {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t) (h13 : t.gpr .r13 = dp s) (hdi : t.gpr .rdi = sb s) :
    WP isa init t fun t' => Mid P s t' ∧ t'.gpr .r13 = dp s ∧ H.stateAt t'.mem (sb s) = iv := by
  have := hF.lt; have := st_le P; have := sc_le P
  have hsub : Region.Sub ⟨sb s, P.N + P.B⟩ (wR P s) := Region.sub_prefix (by omega)
  have hcov : Covers [⟨sb s, P.N + P.B⟩] t.wr :=
    covers_w hp h.wr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, sb_zero s, show 0 + (P.N + P.B) ≤ scratchBytes P by omega⟩
  refine WP.inline hi (rd := []) (wr := [⟨sb s, P.N + P.B⟩])
    ⟨rfl, by simp [State.withRegions, hdi], by simpa [State.withRegions, hdi, h.rsp] using hp.ret_w.sub_right hsub⟩
    (Covers.right hcov) hcov (fun t' hrd hwr _ hf hg hpost => ?_) hin
  have hk : ∀ r, r ≠ .rax → t'.gpr r = t.gpr r := fun r hr => hg r (hiw r hr)
  refine ⟨Mid.of_frame hd h hrd hwr (fun r hr => hk r (mid_ne r hr _ (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hsub⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.base_disjoint _ (by omega) (by omega) : Region.Disjoint ⟨sb s, P.N + P.B⟩ (slR P s)).symm),
    (hk _ (by decide)).trans h13, ?_⟩
  have := (show H.Repr iv t'.mem (sb s) [] by simpa [initK, State.withRegions, hdi] using hpost).1
  simpa [Md.compressList_zero] using this

/-! ## The whole blocks -/

theorem wp_shl {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d <<< n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shl d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (64 - n)))
    (if n = 1 then some ((s.gpr d <<< n).msb ^^ (s.gpr d).getLsbD (64 - n)) else none)
    (some ((s.gpr d <<< n) == 0)) (some (s.gpr d <<< n).msb)).setReg d (s.gpr d <<< n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩

theorem shr_lg {P : Params} (hd : Dims P) {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> Nat.log2 P.B = BitVec.ofNat 64 (n / P.B) := by
  obtain ⟨_, _, h⟩ := hd.lg
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n P.B; omega)]

theorem shl_lg {P : Params} (hd : Dims P) {k : Nat} (hk : P.B * k < 2 ^ 64) :
    BitVec.ofNat 64 k <<< Nat.log2 P.B = BitVec.ofNat 64 (P.B * k) := by
  obtain ⟨_, _, h⟩ := hd.lg
  have hB := hd.pos
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, h,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by
      have : k ≤ P.B * k := Nat.le_mul_of_pos_left k hB
      omega), Nat.mul_comm]

/-! ## Calling the compression function -/

/-- The call's arguments: the first `n` bytes of the message, or the block. -/
theorem callOk_data {P : Params} (hF : Fits P) {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t)
    (hsi : t.gpr .rsi = dp s) {n : Nat} (hn : n ≤ len s) :
    CallOkN P t (sb s) (sb s + BitVec.ofNat 64 (scO P)) (dp s) n := by
  have hsub : Region.Sub ⟨dp s, n⟩ (dR s) := Region.sub_prefix hn
  have hsp := h.rsp
  refine ⟨h.rbx, h.r15, hsi, ?_, (hp.d_w.sub_left hsub).sub_right (h_sub s),
    (hp.d_w.sub_left hsub).sub_right (sc_sub s), by rw [hsp]; exact hp.stk_w.sub_right (h_sub s),
    by rw [hsp]; exact hp.stk_w.sub_right (sc_sub s), by rw [hsp]; exact hp.stk_d.sub_right hsub, ?_, ?_⟩
  · exact h_sc hF s
  · have := hF.lt; have := st_le P; have := sc_le P
    rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dR s, by simp, 0, by simp, by simp only [Nat.zero_add]; exact hn⟩
    · exact ⟨wR P s, by simp, 0, sb_zero s, show 0 + P.N ≤ scratchBytes P by omega⟩
    · exact ⟨wR P s, by simp, scO P, rfl, show scO P + P.so ≤ scratchBytes P by omega⟩
  · have := hF.lt; have := st_le P; have := sc_le P
    exact covers_w hp h.wr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, sb_zero s, show 0 + P.N ≤ scratchBytes P by omega⟩
      · exact ⟨scO P, rfl, show scO P + P.so ≤ scratchBytes P by omega⟩

/-- What a call of the compression function from the body keeps. -/
theorem call_mid {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t t' : State} (hp : Pre P D s)
    (h : Mid P s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [hR P s, ⟨sb s + BitVec.ofNat 64 (scO P), P.so⟩, below (t.gpr .rsp) 8] t.mem t'.mem) :
    Mid P s t' := by
  rw [h.rsp] at hf
  exact Mid.of_frame hd h hrd hwr (fun r hr => hcs r (mid_cs r hr)) hf
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., h_sub s⟩
      · exact ⟨_, List.mem_cons_self .., sc_sub s⟩
      · exact ⟨stkR s, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h_sl hF s).symm
      · exact (sc_sl hF s).symm
      · exact (hp.stk_w.sub_right (sl_sub s)).symm)

theorem whole_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} {iv : H.HV}
    {name : String} {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hp : Pre P D s)
    (h : Mid P s t) (h13 : t.gpr .r13 = dp s) (hiv : H.stateAt t.mem (sb s) = iv) :
    WP isa (whole P name code) t fun t' => Mid P s t' ∧
      t'.gpr .r13 = dp s + BitVec.ofNat 64 (P.B * (len s / P.B)) ∧
      H.stateAt t'.mem (sb s) = H.compressList iv (msg s) (len s / P.B) := by
  have := hF.lt; have := st_le P; have := sc_le P; have hB := hd.pos; have := hd.N; have := hd.so
  have hlen := len_lt s
  have hle : P.B * (len s / P.B) ≤ len s := Nat.mul_div_le _ _
  have hdl : len s / P.B ≤ len s := Nat.div_le_self _ _
  unfold whole
  refine WP.seq (WP.mono (Q := fun (t' : State) => t'.gpr .r14 = BitVec.ofNat 64 (len s / P.B) ∧ Mid P s t' ∧
      t'.gpr .r13 = dp s ∧ t'.mem = t.mem ∧ t'.zf = some (decide (len s / P.B = 0)))
    (wp_mov fun t₁ u₁ _ _ => wp_shr ⟨hd.lg.1, hd.lg.2.1⟩ fun t₂ u₂ => wp_test fun t₃ g₃ m₃ rd₃ wr₃ z₃ =>
      WP.block_nil ?_) fun t₃ ⟨h14, m₃, h13₃, hm₃, hz₃⟩ => ?_)
  · have h14 : t₂.gpr .r14 = BitVec.ofNat 64 (len s / P.B) := by
      rw [u₂.gpr, u₁.gpr, h.r12, rsi_eq, shr_lg hd hlen]
    have k : ∀ r, r ≠ .r14 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.other r hr, u₁.other r hr]
    refine ⟨by rw [g₃, h14], Mid.of_regs hd h (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
        (by rw [m₃, u₂.mem, u₁.mem]) (fun r hr => by rw [g₃, k r (mid_ne r hr _ (by decide))]),
      by rw [g₃, k _ (by decide), h13], by rw [m₃, u₂.mem, u₁.mem], ?_⟩
    rw [z₃, h14, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (len s / P.B = 0)) (by simp [eval, hz₃]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨m₃, by rw [h13₃, hb]; simp, ?_⟩
    rw [hb, Md.compressList_zero, hm₃, hiv]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (wp_mov fun t₄ u₄ _ _ => WP.block_nil ?_)
    have m₄ : Mid P s t₄ := Mid.of_regs hd m₃ u₄.rd u₄.wr u₄.mem
      (fun r hr => u₄.other r (mid_ne r hr _ (by decide)))
    have h14₄ : t₄.gpr .r14 = BitVec.ofNat 64 (len s / P.B) := (u₄.other _ (by decide)).trans h14
    have h13₄ : t₄.gpr .r13 = dp s := (u₄.other _ (by decide)).trans h13₃
    refine WP.seq (compressWith_ok H setsN_r14 hf (k := len s / P.B)
      (by rw [h14₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      (callOk_data hF hp m₄ (by rw [u₄.gpr, h13₃]) hle) (by omega) (by omega)
      fun t₅ hrd hwr hcs hfr hst _ _ => ?_)
    have m₅ := call_mid hF hd hp m₄ hrd hwr hcs hfr
    refine wp_mov fun t₆ u₆ _ _ => wp_shl ⟨hd.lg.1, hd.lg.2.1⟩ fun t₇ u₇ => wp_add fun t₈ u₈ => WP.block_nil ?_
    have h14₅ : t₅.gpr .r14 = BitVec.ofNat 64 (len s / P.B) := (hcs _ (by decide)).trans h14₄
    have h13₅ : t₅.gpr .r13 = dp s := (hcs _ (by decide)).trans h13₄
    refine ⟨Mid.of_regs hd m₅ (by rw [u₈.rd, u₇.rd, u₆.rd]) (by rw [u₈.wr, u₇.wr, u₆.wr])
        (by rw [u₈.mem, u₇.mem, u₆.mem])
        (fun r hr => by
          rw [u₈.other _ (mid_ne r hr _ (by decide)), u₇.other _ (mid_ne r hr _ (by decide)),
            u₆.other _ (mid_ne r hr _ (by decide))]), ?_, ?_⟩
    · rw [u₈.gpr, u₇.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₆.gpr, h13₅, h14₅,
        shl_lg hd (by omega)]
    · rw [u₈.mem, u₇.mem, u₆.mem, hst, u₄.mem, hm₃, hiv]
      exact Md.compressBlocks_eq H fun j hj => data_eq hp h (by omega)

end VG.Proof.MdStream.X86_64.OneShot
