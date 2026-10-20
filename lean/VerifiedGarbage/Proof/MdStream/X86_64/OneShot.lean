module

public import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.MdStream.OneShot
public import VerifiedGarbage.Impl.MdStream.X86_64.OneShot
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset

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

theorem sx16 : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide

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

theorem wholeHead_ok {P : Params} (hd : Dims P) {s t : State} (h : Mid P s t) :
    WP isa (.block (wholeHead P)) t fun t' => Mid P s t' ∧ t'.gpr .r14 = BitVec.ofNat 64 (len s / P.B) ∧
      t'.zf = some (decide (len s / P.B = 0)) ∧ t'.mem = t.mem ∧ ∀ r, r ≠ .r14 → t'.gpr r = t.gpr r := by
  have hlen := len_lt s
  have hdl : len s / P.B ≤ len s := Nat.div_le_self _ _
  unfold wholeHead
  refine wp_mov fun t₁ u₁ _ _ => wp_shr ⟨hd.lg.1, hd.lg.2.1⟩ fun t₂ u₂ => wp_test fun t₃ g₃ m₃ rd₃ wr₃ z₃ =>
    WP.block_nil ?_
  have h14 : t₂.gpr .r14 = BitVec.ofNat 64 (len s / P.B) := by
    rw [u₂.gpr, u₁.gpr, h.r12, rsi_eq, shr_lg hd hlen]
  have k : ∀ r, r ≠ .r14 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.other r hr, u₁.other r hr]
  refine ⟨Mid.of_regs hd h (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
      (by rw [m₃, u₂.mem, u₁.mem]) (fun r hr => by rw [g₃, k r (mid_ne r hr _ (by decide))]),
    by rw [g₃, h14], ?_, by rw [m₃, u₂.mem, u₁.mem], fun r hr => by rw [g₃, k r hr]⟩
  rw [z₃, h14, BitVec.and_self, ofNat_beq_zero (by omega)]

theorem wholeArg_ok {P : Params} (hd : Dims P) {s t : State} (h : Mid P s t) :
    WP isa (.block [.mov .rsi (.reg .r13)]) t fun t' => Mid P s t' ∧ t'.gpr .rsi = t.gpr .r13 ∧
      t'.mem = t.mem ∧ ∀ r, r ≠ .rsi → t'.gpr r = t.gpr r :=
  wp_mov fun t₁ u₁ _ _ => WP.block_nil ⟨Mid.of_regs hd h u₁.rd u₁.wr u₁.mem
    (fun r hr => u₁.other r (mid_ne r hr _ (by decide))), u₁.gpr, u₁.mem, u₁.other⟩

theorem wholeEnd_ok {P : Params} (hd : Dims P) {s t : State} (h : Mid P s t) {k : Nat} (hk : P.B * k < 2 ^ 64)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 k) :
    WP isa (.block (wholeEnd P)) t fun t' => Mid P s t' ∧
      t'.gpr .r13 = t.gpr .r13 + BitVec.ofNat 64 (P.B * k) ∧ t'.mem = t.mem := by
  unfold wholeEnd
  refine wp_mov fun t₆ u₆ _ _ => wp_shl ⟨hd.lg.1, hd.lg.2.1⟩ fun t₇ u₇ => wp_add fun t₈ u₈ => WP.block_nil ?_
  refine ⟨Mid.of_regs hd h (by rw [u₈.rd, u₇.rd, u₆.rd]) (by rw [u₈.wr, u₇.wr, u₆.wr])
      (by rw [u₈.mem, u₇.mem, u₆.mem])
      (fun r hr => by
        rw [u₈.other _ (mid_ne r hr _ (by decide)), u₇.other _ (mid_ne r hr _ (by decide)),
          u₆.other _ (mid_ne r hr _ (by decide))]), ?_, by rw [u₈.mem, u₇.mem, u₆.mem]⟩
  rw [u₈.gpr, u₇.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₆.gpr, h14, shl_lg hd hk]

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
  refine WP.seq (WP.mono (wholeHead_ok hd h) fun t₃ ⟨m₃, h14, hz₃, hm₃, g₃⟩ => ?_)
  have h13₃ : t₃.gpr .r13 = dp s := (g₃ _ (by decide)).trans h13
  refine WP.ite (decide (len s / P.B = 0)) (by simp [eval, hz₃]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨m₃, by rw [h13₃, hb]; simp, ?_⟩
    rw [hb, Md.compressList_zero, hm₃, hiv]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (wholeArg_ok hd m₃) fun t₄ ⟨m₄, hsi₄, hm₄, g₄⟩ => ?_)
    have h14₄ : t₄.gpr .r14 = BitVec.ofNat 64 (len s / P.B) := (g₄ _ (by decide)).trans h14
    have h13₄ : t₄.gpr .r13 = dp s := (g₄ _ (by decide)).trans h13₃
    refine WP.seq (compressWith_ok H setsN_r14 hf (k := len s / P.B)
      (by rw [h14₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      (callOk_data hF hp m₄ (by rw [hsi₄, h13₃]) hle) (by omega) (by omega)
      fun t₅ hrd hwr hcs hfr hst _ _ => ?_)
    have m₅ := call_mid hF hd hp m₄ hrd hwr hcs hfr
    have h14₅ : t₅.gpr .r14 = BitVec.ofNat 64 (len s / P.B) := (hcs _ (by decide)).trans h14₄
    have h13₅ : t₅.gpr .r13 = dp s := (hcs _ (by decide)).trans h13₄
    refine WP.mono (wholeEnd_ok hd m₅ (by omega) h14₅) fun t₈ ⟨m₈, h13₈, hm₈⟩ => ⟨m₈, by rw [h13₈, h13₅], ?_⟩
    rw [hm₈, hst, hm₄, hm₃, hiv]
    exact Md.compressBlocks_eq H fun j hj => data_eq hp h (by omega)

/-! ## The block -/

section
variable (P : Params) (s : State)

/-- The bytes of the message after its whole blocks. -/
abbrev rem : Nat := len s % P.B
/-- Where they start. -/
abbrev whl : Nat := P.B * (len s / P.B)

end

theorem whl_rem (P : Params) (s : State) : whl P s + rem P s = len s := Nat.div_add_mod _ _

/-- The block holds the first `c` bytes after the whole blocks of the
message, then zeros. -/
def Blk (P : Params) (s : State) (c : Nat) (m : Mem) : Prop :=
  ∀ j < P.B, m (sb s + BitVec.ofNat 64 (P.N + j)) = if j < c then (msg s).getD (whl P s + j) 0 else 0

/-- The block holds the bytes left, `0x80`, then zeros. -/
def Blk80 (P : Params) (s : State) (m : Mem) : Prop :=
  ∀ j < P.B, m (sb s + BitVec.ofNat 64 (P.N + j)) =
    if j < rem P s then (msg s).getD (whl P s + j) 0 else if j = rem P s then 0x80 else 0

theorem wp_movdquLoad {is : List Instr} {s : State} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : WP isa (.block is) (s.setXmm d (s.mem.readW a 128)) Q) :
    WP isa (.block (.movdquLoad d m :: is)) s Q :=
  WP.cons (by simp [exec, State.load128, ha, hin]) k

theorem ea_at' (t : State) (b : Reg) (d : Nat) : t.ea (at_ b d) = t.gpr b + BitVec.ofNat 64 d := by
  rw [ea_at, ofInt_natCast]

/-- `zeroBuf`'s stores: the first `n` 16-byte words of the block. -/
theorem zeros_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s : State} (hp : Pre P D s) (n : Nat)
    (hn : n ≤ P.B / 16) {t : State} (hbx : t.gpr .rbx = sb s) (hx : t.xmm .xmm0 = 0) (hwr : t.wr = s.wr) :
    WP isa (.block ((List.range n).map fun k => .movdquStore (at_ .rbx (P.N + 16 * k)) .xmm0)) t fun t' =>
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.xmm = t.xmm ∧ Frame [bR P s] t.mem t'.mem ∧
      ∀ j < 16 * n, t'.mem (sb s + BitVec.ofNat 64 (P.N + j)) = 0 := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t₁ ⟨g₁, rd₁, wr₁, x₁, f₁, z₁⟩ => ?_
    have hb : 16 * n + 16 ≤ P.B := by omega
    refine wp_movdquStoreX (a := sb s + BitVec.ofNat 64 (P.N + 16 * n)) (by rw [ea_at', g₁, hbx])
      ⟨wR P s, by rw [wr₁, hwr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
      fun t₂ g₂ m₂ rd₂ wr₂ x₂ => WP.block_nil ?_
    refine ⟨by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [x₂, x₁], ?_, fun j hj => ?_⟩
    · rw [m₂]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [← add_ofNat]; exact Offset.contains_base _ (by omega) (by omega))
    · rw [m₂, x₁, hx, writeW128_off _ _ _ (by omega) (by omega)]
      split
      · simp
      · exact z₁ j (by omega)

/-- `zeroBuf`: the block is zero. -/
theorem zeroBuf_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t : State} (hp : Pre P D s)
    (h : Mid P s t) :
    WP isa (.block (zeroBuf P)) t fun t' => Mid P s t' ∧ t'.gpr = t.gpr ∧ Frame [bR P s] t.mem t'.mem ∧
      Blk P s 0 t'.mem := by
  have := hd.B
  unfold zeroBuf
  refine wp_xbin ?_
  have hx : (t.setXmm .xmm0 (XBinOp.pxor.eval (t.xmm .xmm0) (t.xmm .xmm0))).xmm .xmm0 = 0 := by
    simp [State.setXmm, XBinOp.eval]
  refine WP.mono (zeros_ok hF hd hp (P.B / 16) (Nat.le_refl _) h.rbx hx h.wr)
    fun t₃ ⟨g₃, rd₃, wr₃, _, f₃, z₃⟩ => ?_
  refine ⟨Mid.of_blk hF hd h rd₃ wr₃ (fun r _ => by rw [g₃]; rfl) f₃, by rw [g₃]; rfl, f₃, fun j hj => ?_⟩
  rw [z₃ j (by rcases hd.B with h | h <;> omega)]
  simp

/-! ## Counting loops -/

/-- `if zf skip else do body while ¬zf`, with `zf` iff `K = 0` on entry and
each iteration `i < K` leaving `zf` iff it was the last. -/
theorem count_loop {body : Prog isa} {I : Nat → State → Prop} {K : Nat}
    (hstep : ∀ i < K, ∀ t, I i t →
      WP isa body t fun t' => I (i + 1) t' ∧ t'.zf = some (decide (K - (i + 1) = 0)))
    {t : State} (h₀ : I 0 t) (hz : t.zf = some (decide (K = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) t (I K) := by
  refine WP.ite (decide (K = 0)) (by simp [eval, hz]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb; exact WP.block_nil h₀
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n t => ∃ i, n = K - i ∧ i < K ∧ I i t)
      ?_ K t ⟨0, rfl, by omega, h₀⟩
    rintro n t ⟨i, rfl, hi, hI⟩
    refine WP.mono (hstep i hi t hI) fun t' ⟨hI', hz'⟩ => ?_
    by_cases hl : K - (i + 1) = 0
    · refine .inl ⟨by simp [eval, hz', hl], ?_⟩
      rwa [show i + 1 = K by omega] at hI'
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, i + 1, rfl, by omega, hI'⟩

/-! ## Copying the bytes left -/

/-- Copying, from the state `t₀`: `c` bytes copied. -/
structure CInv (P : Params) (s t₀ : State) (c : Nat) (t : State) : Prop where
  mid : Mid P s t
  c_le : c ≤ rem P s
  r13 : t.gpr .r13 = dp s + BitVec.ofNat 64 (whl P s + c)
  r11 : t.gpr .r11 = BitVec.ofNat 64 c
  r10 : t.gpr .r10 = BitVec.ofNat 64 (rem P s)
  frame : Frame [bR P s] t₀.mem t.mem
  blk : Blk P s c t.mem

theorem ea_blk {P : Params} (t : State) {b : Addr} {c : Nat} (hb : t.gpr .rbx = b)
    (hc : t.gpr .r11 = BitVec.ofNat 64 c) : t.ea (blkByte P) = b + BitVec.ofNat 64 (P.N + c) := by
  simp only [State.ea, blkByte, hb, hc, BitVec.mul_one, ofInt_natCast]
  rw [add_ofNat, Nat.add_comm]

theorem copy16_step {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t₀ t : State} (hp : Pre P D s)
    {c k : Nat} (hc : c + 16 ≤ rem P s) (h : CInv P s t₀ c t) (h9 : t.gpr .r9 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkl : k < 2 ^ 64) :
    WP isa (.block (copy16 P)) t fun t' => CInv P s t₀ (c + 16) t' ∧ t'.gpr .r9 = BitVec.ofNat 64 (k - 1) ∧
      t'.zf = some (decide (k - 1 = 0)) := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N
  have hwr := whl_rem P s; have hlen := len_lt s
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hm := h.mid
  unfold copy16
  refine wp_movdquLoad (a := dp s + BitVec.ofNat 64 (whl P s + c)) (by simp [State.ea, h.r13])
    ⟨dR s, by rw [hm.rd, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩ ?_
  refine wp_movdquStore (a := sb s + BitVec.ofNat 64 (P.N + c)) (ea_blk _ hm.rbx h.r11)
    ⟨wR P s, by simp [State.setXmm, hm.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
    fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r9 → r ≠ .r11 → r ≠ .r13 → t₅.gpr r = t.gpr r := fun r h1 h2 h3 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂]; rfl
  have mem₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [bR P s] t.mem t₂.mem := by
    rw [m₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [← add_ofNat]; exact Offset.contains_base _ (by omega) (by omega))
  have h9₅ : t₅.gpr .r9 = BitVec.ofNat 64 (k - 1) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    show t.gpr .r9 - _ = _
    rw [h9, sx1, ofNat_pred hk]
  refine ⟨⟨Mid.of_blk hF hd hm (by rw [u₅.rd, u₄.rd, u₃.rd, rd₂]; rfl) (by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]; rfl)
      (fun r hr => g r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)))
      (by rw [mem₅]; exact fr₂),
    by omega, ?_, ?_, ?_, by rw [mem₅]; exact h.frame.trans fr₂, fun j hj => ?_⟩, h9₅, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂]
    show t.gpr .r13 + _ = _
    rw [h.r13, sx16, add_ofNat, Nat.add_assoc]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂]
    show t.gpr .r11 + _ = _
    rw [h.r11, sx16, ← BitVec.ofNat_add]
  · rw [g _ (by decide) (by decide) (by decide), h.r10]
  · rw [mem₅, m₂, writeW128_off _ _ _ (by omega) (by omega)]
    simp only [State.setXmm, ite_true]
    split
    · rw [readW128_byte _ _ (by omega), add_ofNat, data_eq hp hm (by omega), itp (show j < c + 16 by omega)]
      exact getD_congr (by omega)
    rw [h.blk j hj]
    by_cases hjc : j < c
    · rw [itp hjc, itp (show j < c + 16 by omega)]
    · rw [itn hjc, itn (show ¬ j < c + 16 by omega)]
  · rw [hz₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    show some (t.gpr .r9 - _ == 0) = _
    rw [h9, sx1, ofNat_pred hk, ofNat_beq_zero (by omega)]

theorem copy1_step {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t₀ t : State} (hp : Pre P D s)
    {c k : Nat} (hc : c + 1 ≤ rem P s) (h : CInv P s t₀ c t) (hax : t.gpr .rax = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkl : k < 2 ^ 64) :
    WP isa (.block (copy1 P)) t fun t' => CInv P s t₀ (c + 1) t' ∧ t'.gpr .rax = BitVec.ofNat 64 (k - 1) ∧
      t'.zf = some (decide (k - 1 = 0)) := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N
  have hwr := whl_rem P s; have hlen := len_lt s
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hm := h.mid
  unfold copy1
  refine wp_movzx8 (a := dp s + BitVec.ofNat 64 (whl P s + c)) (by simp [State.ea, h.r13])
    ⟨dR s, by rw [hm.rd, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩ fun t₁ u₁ => ?_
  refine wp_store8 (a := sb s + BitVec.ofNat 64 (P.N + c))
    (ea_blk _ (by rw [u₁.other _ (by decide), hm.rbx]) (by rw [u₁.other _ (by decide), h.r11]))
    ⟨wR P s, by rw [u₁.wr, hm.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
    fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r11 → r ≠ .r13 → r ≠ .r8 → t₅.gpr r = t.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂, u₁.other r h4]
  have mem₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [bR P s] t.mem t₂.mem := by
    rw [m₂, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [← add_ofNat]; exact Offset.contains_base _ (by omega) (by omega))
  have hax₄ : t₄.gpr .rax = BitVec.ofNat 64 k := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hax]
  refine ⟨⟨Mid.of_blk hF hd hm (by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr])
      (fun r hr => g r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))
        (mid_ne r hr _ (by decide)))
      (by rw [mem₅]; exact fr₂),
    by omega, ?_, ?_, ?_, by rw [mem₅]; exact h.frame.trans fr₂, fun j hj => ?_⟩, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), h.r13, sx1,
      ← Nat.add_assoc, ofNat_succ, BitVec.add_assoc]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.r11, sx1,
      ofNat_succ]
  · rw [g _ (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [mem₅, m₂, u₁.mem, writeW8_off _ _ _ (by omega) (by omega)]
    split
    · rw [itp (show j < c + 1 by omega), u₁.gpr, data_eq hp hm (by omega), show j = c by omega]
      ext i hi; simp
    rw [h.blk j hj]
    by_cases hjc : j < c
    · rw [itp hjc, itp (show j < c + 1 by omega)]
    · rw [itn hjc, itn (show ¬ j < c + 1 by omega)]
  · rw [u₅.gpr, hax₄, sx1, ofNat_pred hk]
  · rw [hz₅, hax₄, sx1, ofNat_pred hk, ofNat_beq_zero (by omega)]

theorem wp_andiZ {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → s'.zf = some (s.gpr d &&& v.signExtend 64 == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_shrZ {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.zf = some (s.gpr d >>> n == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_ rfl)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩

theorem and15 (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 16) := by
  rw [show BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 (2 ^ 4 - 1) by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (2 ^ 4 - 1 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]

theorem copyTail_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t : State} (hp : Pre P D s)
    (h : Mid P s t) (h13 : t.gpr .r13 = dp s + BitVec.ofNat 64 (whl P s)) (hb : Blk P s 0 t.mem) :
    WP isa (copyTail P) t fun t' => Mid P s t' ∧ t'.gpr .r10 = BitVec.ofNat 64 (rem P s) ∧
      Frame [bR P s] t.mem t'.mem ∧ Blk80 P s t'.mem := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  have hlen := len_lt s
  unfold copyTail
  refine WP.seq (WP.mono (Q := fun (t' : State) => CInv P s t 0 t' ∧ t'.gpr .r9 = BitVec.ofNat 64 (rem P s / 16) ∧
      t'.zf = some (decide (rem P s / 16 = 0)))
    (wp_mov fun t₁ u₁ _ _ => wp_andi fun t₂ u₂ => wp_mov32i fun t₃ u₃ _ _ => wp_mov fun t₄ u₄ _ _ =>
      wp_shrZ (by decide) fun t₅ u₅ hz₅ => WP.block_nil ?_) fun t₅ ⟨hI₅, h9₅, hz₅⟩ => ?_)
  · have g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t₅.gpr r = t.gpr r := fun r h9 h10 h11 => by
      rw [u₅.other _ h9, u₄.other _ h9, u₃.other _ h11, u₂.other _ h10, u₁.other _ h10]
    have h10 : t₂.gpr .r10 = BitVec.ofNat 64 (rem P s) := by
      rw [u₂.gpr, u₁.gpr, h.r12, and_mask hd.B]
    have h10₅ : t₅.gpr .r10 = BitVec.ofNat 64 (rem P s) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), h10]
    have h9₅ : t₅.gpr .r9 = BitVec.ofNat 64 (rem P s / 16) := by
      rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), h10, shr4 (by omega)]
    have mem₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ⟨⟨Mid.of_regs hd h (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
        mem₅ (fun r hr => g r (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide)) (mid_ne r hr _ (by decide))),
      Nat.zero_le _, by rw [g _ (by decide) (by decide) (by decide), h13]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; rfl, h10₅,
      by rw [mem₅]; exact Frame.refl _ _, by rw [mem₅]; exact hb⟩, h9₅, ?_⟩
    rw [hz₅, u₄.gpr, u₃.other _ (by decide), h10, shr4 (by omega), ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (count_loop (K := rem P s / 16)
      (I := fun i t' => CInv P s t (16 * i) t' ∧ t'.gpr .r9 = BitVec.ofNat 64 (rem P s / 16 - i))
      (fun i hi t' ⟨hI, h9'⟩ => WP.mono (copy16_step hF hd hp (k := rem P s / 16 - i) (by omega) hI h9'
          (by omega) (by omega))
        fun t'' ⟨hI'', h9'', hz''⟩ => ⟨⟨by rwa [show 16 * (i + 1) = 16 * i + 16 by omega], by
          rw [h9'', Nat.sub_sub]⟩, by rw [hz'', Nat.sub_sub]⟩)
      ⟨hI₅, by rw [h9₅, Nat.sub_zero]⟩ hz₅) fun t₆ ⟨hI₆, _⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (t' : State) => CInv P s t (16 * (rem P s / 16) + 0) t' ∧
      t'.gpr .rax = BitVec.ofNat 64 (rem P s % 16) ∧ t'.zf = some (decide (rem P s % 16 = 0)))
    (wp_mov fun t₇ u₇ _ _ => wp_andiZ fun t₈ u₈ hz₈ => WP.block_nil ?_) fun t₈ ⟨hI₈, hax₈, hz₈⟩ => ?_)
  · have g : ∀ r, r ≠ .rax → t₈.gpr r = t₆.gpr r := fun r hr => by rw [u₈.other _ hr, u₇.other _ hr]
    have hax : t₈.gpr .rax = BitVec.ofNat 64 (rem P s % 16) := by
      rw [u₈.gpr, u₇.gpr, hI₆.r10, and15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show rem P s < 2 ^ 64 by omega)]
    have mem₈ : t₈.mem = t₆.mem := by rw [u₈.mem, u₇.mem]
    refine ⟨⟨Mid.of_regs hd hI₆.mid (by rw [u₈.rd, u₇.rd]) (by rw [u₈.wr, u₇.wr]) mem₈
        (fun r hr => g r (mid_ne r hr _ (by decide))),
      by have := hI₆.c_le; omega, by rw [g _ (by decide), hI₆.r13, Nat.add_zero],
      by rw [g _ (by decide), hI₆.r11, Nat.add_zero], by rw [g _ (by decide), hI₆.r10],
      by rw [mem₈]; exact hI₆.frame, by rw [mem₈, Nat.add_zero]; exact hI₆.blk⟩, hax, ?_⟩
    rw [hz₈, ← u₈.gpr, hax, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (count_loop (K := rem P s % 16)
      (I := fun i t' => CInv P s t (16 * (rem P s / 16) + i) t' ∧ t'.gpr .rax = BitVec.ofNat 64 (rem P s % 16 - i))
      (fun i hi t' ⟨hI, hax'⟩ => WP.mono (copy1_step hF hd hp (k := rem P s % 16 - i) (by omega) hI hax'
          (by omega) (by omega))
        fun t'' ⟨hI'', hax'', hz''⟩ => ⟨⟨by rwa [Nat.add_assoc] at hI'', by rw [hax'', Nat.sub_sub]⟩,
          by rw [hz'', Nat.sub_sub]⟩)
      ⟨hI₈, by rw [hax₈, Nat.sub_zero]⟩ hz₈) fun t₉ ⟨hI₉, _⟩ => ?_)
  have hc : 16 * (rem P s / 16) + rem P s % 16 = rem P s := Nat.div_add_mod _ _
  rw [hc] at hI₉
  have hm₉ := hI₉.mid
  refine wp_mov32i fun t₁₀ u₁₀ _ _ => wp_store8 (a := sb s + BitVec.ofNat 64 (P.N + rem P s))
    (ea_blk _ (by rw [u₁₀.other _ (by decide), hm₉.rbx]) (by rw [u₁₀.other _ (by decide), hI₉.r11]))
    ⟨wR P s, by rw [u₁₀.wr, hm₉.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
    fun t₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ => WP.block_nil ?_
  have fr : Frame [bR P s] t₉.mem t₁₁.mem := by
    rw [m₁₁, u₁₀.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [← add_ofNat]; exact Offset.contains_base _ (by omega) (by omega))
  refine ⟨Mid.of_blk hF hd hm₉ (by rw [rd₁₁, u₁₀.rd]) (by rw [wr₁₁, u₁₀.wr])
      (fun r hr => by rw [g₁₁, u₁₀.other _ (mid_ne r hr _ (by decide))]) fr,
    by rw [g₁₁, u₁₀.other _ (by decide), hI₉.r10], hI₉.frame.trans fr, fun j hj => ?_⟩
  rw [m₁₁, u₁₀.mem, u₁₀.gpr, writeW8_off _ _ _ (by omega) (by omega)]
  split
  · rw [itn (show ¬ j < rem P s by omega), itp (show j = rem P s by omega)]; rfl
  rw [hI₉.blk j hj]
  by_cases hjc : j < rem P s
  · rw [itp hjc, itp hjc]
  · rw [itn hjc, itn hjc, itn (show ¬ j = rem P s by omega)]

/-! ## Compressing the block -/

/-- The block's address, in `rsi`. -/
theorem blkArg_ok {P : Params} (hF : Fits P) (hd : Dims P) {s t : State} (h : Mid P s t) :
    WP isa (.block (blkArg P)) t fun t' => Mid P s t' ∧ t'.gpr .rsi = sb s + BitVec.ofNat 64 P.N ∧
      t'.mem = t.mem ∧ ∀ r, r ≠ .rsi → t'.gpr r = t.gpr r := by
  have := hF.lt; have := st_le P; have := sc_le P
  unfold blkArg
  refine wp_mov fun t₁ u₁ _ _ => wp_addi fun t₂ u₂ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rsi → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.other r hr, u₁.other r hr]
  refine ⟨Mid.of_regs hd h (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.mem, u₁.mem])
      (fun r hr => k r (mid_ne r hr _ (by decide))), ?_, by rw [u₂.mem, u₁.mem], k⟩
  rw [u₂.gpr, u₁.gpr, h.rbx, sx_lt (by omega)]

/-- The call's arguments for the block. -/
theorem callOk_buf {P : Params} (hF : Fits P) {D : Nat} {s t : State} (hp : Pre P D s) (h : Mid P s t)
    (hsi : t.gpr .rsi = sb s + BitVec.ofNat 64 P.N) :
    CallOk P t (sb s) (sb s + BitVec.ofNat 64 (scO P)) (sb s + BitVec.ofNat 64 P.N) := by
  have := hF.lt; have := st_le P; have := sc_le P
  have hsp := h.rsp
  refine ⟨h.rbx, h.r15, hsi, h_sc hF s, (h_b hF s).symm, b_sc hF s,
    by rw [hsp]; exact hp.stk_w.sub_right (h_sub s), by rw [hsp]; exact hp.stk_w.sub_right (sc_sub s),
    by rw [hsp]; exact hp.stk_w.sub_right (b_sub s), Covers.right (covers_w hp h.wr ?_), covers_w hp h.wr ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨P.N, rfl, show P.N + P.B ≤ scratchBytes P by omega⟩
    · exact ⟨0, sb_zero s, show 0 + P.N ≤ scratchBytes P by omega⟩
    · exact ⟨scO P, rfl, show scO P + P.so ≤ scratchBytes P by omega⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, sb_zero s, show 0 + P.N ≤ scratchBytes P by omega⟩
    · exact ⟨scO P, rfl, show scO P + P.so ≤ scratchBytes P by omega⟩

theorem stateAt_bframe {P : Params} {H : Md P.B P.N P.L} (hF : Fits P) {s : State} {m m' : Mem}
    (hf : Frame [bR P s] m m') : H.stateAt m' (sb s) = H.stateAt m (sb s) :=
  H.stateAt_congr fun i hi => hf.bytes (R := hR P s)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h_b hF s)
    (by have := hF.lt; have := st_le P; have := sc_le P; show P.N ≤ 2 ^ 64; omega) hi

/-- Compressing the block, with its address in `rsi`. -/
theorem compressBuf_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} {name : String}
    {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hp : Pre P D s) (h : Mid P s t)
    (hsi : t.gpr .rsi = sb s + BitVec.ofNat 64 P.N) {Q : State → Prop}
    (hQ : ∀ t', Mid P s t' → Frame [hR P s, ⟨sb s + BitVec.ofNat 64 (scO P), P.so⟩,
        below (s.gpr .rsp) 8] t.mem t'.mem →
      H.stateAt t'.mem (sb s) = H.compress (H.stateAt t.mem (sb s)) (H.blockAt t.mem (sb s + BitVec.ofNat 64 P.N)) →
      Q t') :
    WP isa (compressAt name code) t Q := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N
  refine compressAt_ok H hf (callOk_buf hF hp h hsi) (by omega) (by omega) fun t' hrd hwr hcs hfr hst _ _ => ?_
  refine hQ t' (call_mid hF hd hp h hrd hwr hcs hfr) (by rw [h.rsp] at hfr; exact hfr) hst

/-! ## The length field and the last compression -/

/-- Before the length field: the digest follows from the hash value and the
block's first `B - L` bytes. -/
structure Last {P : Params} (H : Md P.B P.N P.L) (iv : H.HV) (s t : State) : Prop where
  mid : Mid P s t
  hash : H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.compress (H.stateAt t.mem (sb s))
    (H.parse fun j => if j < P.B - P.L then t.mem (sb s + BitVec.ofNat 64 (P.N + j))
      else (H.lenBytes (len s)).getD (j - (P.B - P.L)) 0))

/-- The length field, and the block's address in `rsi`. -/
theorem lenArg_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {s t : State} (hp : Pre P D s) (h : Mid P s t) :
    WP isa (.block (P.len ++ blkArg P)) t fun t' => Mid P s t' ∧ t'.gpr .rsi = sb s + BitVec.ofNat 64 P.N ∧
      Frame [bR P s] t.mem t'.mem ∧
      t'.mem = writeBytes t.mem (sb s + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (BitVec.ofNat 64 (len s))) := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N; have := hd.L
  have hlc : (wR P s).Contains (sb s + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
    Offset.contains_base _ (by omega) (by omega)
  have hin : InRegions t.wr (t.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
    ⟨wR P s, by rw [h.wr, hp.wr]; simp, by rw [h.rbx]; exact hlc⟩
  rw [WP.block_append_iff]
  refine WP.mono (hs.len t hin) fun t₃ ⟨g₃, rd₃, wr₃, m₃⟩ => ?_
  rw [h.rbx, h.r12, rsi_eq] at m₃
  have hlb := H.lenOf_length (BitVec.ofNat 64 (len s))
  have fr₃ : Frame [bR P s] t.mem t₃.mem := by
    rw [m₃]
    exact writeBytes_frame _ _ _ (by rw [hlb, show P.N + P.B - P.L = P.N + (P.B - P.L) by omega, ← add_ofNat]
                                     exact Offset.contains_base _ (by omega) (by omega))
  have m₃' : Mid P s t₃ := Mid.of_blk hF hd h rd₃ wr₃ (fun r hr => g₃ r (mid_ne r hr _ (by decide))) fr₃
  exact WP.mono (blkArg_ok hF hd m₃') fun t₄ ⟨m₄, hsi, hm₄, _⟩ =>
    ⟨m₄, hsi, by rw [hm₄]; exact fr₃, by rw [hm₄, m₃]⟩

theorem lenFin_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hp : Pre P D s)
    (hl : Last H iv s t) :
    WP isa (.seq (.block (P.len ++ blkArg P)) (compressAt name code)) t fun t' =>
      Mid P s t' ∧ (H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.stateAt t'.mem (sb s))) := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N; have := hd.L
  refine WP.seq (WP.mono (lenArg_ok hF hd hs hp hl.mid) fun t₄ ⟨m₄, hsi, fr₄, hm₄⟩ => ?_)
  refine compressBuf_ok hF hd hf hp m₄ hsi fun t₅ m₅ _ hst => ⟨m₅, fun hok => ?_⟩
  rw [hst, stateAt_bframe hF fr₄, hl.hash hok]
  refine congrArg (fun b => H.digest (H.compress _ b)) (H.parse_congr fun k hk => ?_)
  simp only [hm₄, add_ofNat, H.lenOf_eq _ hok]
  rw [writeBytes_off _ _ _ (by rw [H.lenBytes_length]; omega) (by omega), H.lenBytes_length]
  by_cases hkl : k < P.B - P.L
  · rw [itp hkl, itn (show ¬ (P.N + P.B - P.L ≤ P.N + k ∧ P.N + k < P.N + P.B - P.L + P.L) by omega)]
  · rw [itn hkl, itp (show P.N + P.B - P.L ≤ P.N + k ∧ P.N + k < P.N + P.B - P.L + P.L by omega),
      show P.N + k - (P.N + P.B - P.L) = k - (P.B - P.L) by omega]

/-! ## The last block or two -/

theorem blockAt_eq {P : Params} {H : Md P.B P.N P.L} (s : State) (m : Mem) {f : Nat → Byte}
    (h : ∀ k < P.B, m (sb s + BitVec.ofNat 64 (P.N + k)) = f k) :
    H.blockAt m (sb s + BitVec.ofNat 64 P.N) = H.parse f :=
  H.parse_congr fun k hk => by rw [add_ofNat]; exact h k hk

theorem cmpLen_ok {P : Params} (hF : Fits P) (hd : Dims P) {s t : State} (h : Mid P s t)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 (rem P s)) :
    WP isa (.block (cmpLen P)) t fun t' => Mid P s t' ∧ t'.cf = some (decide (rem P s < P.B - P.L)) ∧
      t'.mem = t.mem := by
  have := hF.lt; have := st_le P; have := sc_le P
  have hr : rem P s < P.B := Nat.mod_lt _ hd.pos
  refine wp_cmpi fun t₃ g₃ mem₃ rd₃ wr₃ cf₃ _ => WP.block_nil ⟨Mid.of_regs hd h rd₃ wr₃ mem₃
    (fun r _ => by rw [g₃]), ?_, mem₃⟩
  rw [cf₃, h10, sx_lt (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by have := len_lt s; omega)]

theorem pad1' (P : Params) (s : State) (hr : rem P s + P.L < P.B) {k : Nat} (lb : List Byte)
    (hlb : lb.length = P.L) :
    (Md.rest P.B (msg s) ++ [0x80] ++ List.replicate (P.B - P.L - 1 - rem P s) 0 ++ lb).getD k 0 =
      if k < P.B - P.L then
        (if k < rem P s then (msg s).getD (whl P s + k) 0 else if k = rem P s then 0x80 else 0)
      else lb.getD (k - (P.B - P.L)) 0 := by
  have := pad1_getD P.B (msg s) (L := P.L) (by simpa only [MdStream.OneShot.rem, msg_length] using hr)
    (k := k) lb hlb
  simpa only [MdStream.OneShot.rem, MdStream.OneShot.whl, msg_length] using this

theorem pad2a' (P : Params) (s : State) {k : Nat} :
    (Md.rest P.B (msg s) ++ [0x80] ++ List.replicate (P.B - 1 - rem P s) 0).getD k 0 =
      if k < rem P s then (msg s).getD (whl P s + k) 0 else if k = rem P s then 0x80 else 0 := by
  have := pad2a_getD P.B (msg s) (k := k)
  simpa only [MdStream.OneShot.rem, MdStream.OneShot.whl, msg_length] using this

theorem tail_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s t : State} (hp : Pre P D s)
    (h : Mid P s t) (h13 : t.gpr .r13 = dp s + BitVec.ofNat 64 (whl P s))
    (hw : H.stateAt t.mem (sb s) = H.compressList iv (msg s) (len s / P.B)) :
    WP isa (tail P name code) t fun t' =>
      Mid P s t' ∧ (H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.stateAt t'.mem (sb s))) := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N; have := hd.L
  have hB := hd.pos
  have hr : rem P s < P.B := Nat.mod_lt _ hB
  unfold tail
  refine WP.seq (WP.mono (zeroBuf_ok hF hd hp h) fun t₁ ⟨m₁, g₁, f₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (copyTail_ok hF hd hp m₁ (by rw [g₁, h13]) b₁)
    fun t₂ ⟨m₂, h10₂, f₂, b₂⟩ => ?_)
  have hw₂ : H.stateAt t₂.mem (sb s) = H.compressList iv (msg s) (len s / P.B) := by
    rw [stateAt_bframe hF f₂, stateAt_bframe hF f₁, hw]
  refine WP.seq (WP.mono (cmpLen_ok hF hd m₂ h10₂) fun t₃ ⟨m₃, hcf, mem₃⟩ => ?_)
  have hlen : (msg s).length % P.B = rem P s := by rw [msg_length]
  refine WP.seq (WP.mono (Q := Last H iv s) (WP.ite (decide (P.B - P.L ≤ rem P s)) (by
      simp only [eval, hcf, Option.map_some, Option.some.injEq]
      by_cases hx : rem P s < P.B - P.L <;> simp [hx] <;> omega) (fun hb => ?_) (fun hb => ?_))
    fun t₅ hl => lenFin_ok hF hd hs hf hp hl)
  · -- Two blocks.
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (WP.mono (blkArg_ok hF hd m₃) fun t₄ ⟨m₄, hsi, hm₄, _⟩ => ?_)
    refine WP.seq (compressBuf_ok hF hd hf hp m₄ hsi fun t₅ m₅ _ hst₅ => ?_)
    refine WP.mono (zeroBuf_ok hF hd hp m₅) fun t₆ ⟨m₆, _, f₆, b₆⟩ => ⟨m₆, fun hok => ?_⟩
    rw [H.hash_two hB (by omega) (by rw [hlen]; omega), hlen, msg_length, stateAt_bframe hF f₆, hst₅, hm₄,
      mem₃, hw₂, blockAt_eq (H := H) s t₂.mem (f := fun t => (Md.rest P.B (msg s) ++ [0x80] ++
        List.replicate (P.B - 1 - rem P s) 0).getD t 0) fun k hk => by
          rw [b₂ k hk, pad2a']]
    refine congrArg H.digest (congrArg (H.compress _) (H.parse_congr fun k hk => ?_))
    rw [pad2b_getD]
    by_cases hkl : k < P.B - P.L
    · rw [itp hkl, itp hkl, b₆ k hk]; rfl
    · rw [itn hkl, itn hkl]
  · -- One block.
    simp only [decide_eq_false_iff_not] at hb
    have hr1 : rem P s + P.L < P.B := by omega
    refine WP.block_nil ⟨m₃, fun hok => ?_⟩
    rw [H.hash_one hB (by rw [hlen]; exact hr1), hlen, msg_length, mem₃, hw₂]
    refine congrArg H.digest (congrArg (H.compress _) (H.parse_congr fun k hk => ?_))
    rw [pad1' P s hr1 _ (H.lenBytes_length _)]
    by_cases hkl : k < P.B - P.L
    · rw [itp hkl, itp hkl, b₂ k hk]
    · rw [itn hkl, itn hkl]

/-! ## The digest, zeroing the buffer and restoring the registers -/

/-- `wipe`'s stores: the first `n` 16-byte words of the buffer. -/
theorem wipes_ok {P : Params} (hF : Fits P) {D : Nat} {s : State} (hp : Pre P D s) (n : Nat)
    (hn : 16 * n ≤ scO P) {t : State} (hbx : t.gpr .rbx = sb s) (hwr : t.wr = s.wr) :
    WP isa (.block ((List.range n).map fun k => .movdquStore (at_ .rbx (16 * k)) .xmm0)) t fun t' =>
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ Frame [⟨sb s, scO P⟩] t.mem t'.mem := by
  have := hF.lt; have := sc_le P
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t₁ ⟨g₁, rd₁, wr₁, f₁⟩ => ?_
    refine wp_movdquStore (a := sb s + BitVec.ofNat 64 (16 * n)) (by rw [ea_at', g₁, hbx])
      ⟨wR P s, by rw [wr₁, hwr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
      fun t₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ⟨by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_⟩
    rw [m₂]
    exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- Restoring our caller's registers from their slots, through `r15`. -/
theorem restore_ok {P : Params} (hF : Fits P) (hd : Dims P) {D : Nat} {s t : State} (hp : Pre P D s)
    (hwr : t.wr = s.wr) (hrd : t.rd = s.rd) (h15 : t.gpr .r15 = sb s + BitVec.ofNat 64 (scO P))
    (hsl : Slots P s t.mem) :
    WP isa (.block (restore P)) t fun t' => (∀ p ∈ saved P, t'.gpr p.1 = s.gpr p.1) ∧ t'.mem = t.mem ∧
      t'.gpr .rsp = t.gpr .rsp := by
  have := hF.lt; have := sc_le P; have := hd.so
  have hin : ∀ {u : State}, u.rd = s.rd → u.wr = s.wr → ∀ p ∈ saved P,
      InRegions (u.rd ++ u.wr) (sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (p.2 : Int)) 8 :=
    fun hr hw p hq => ⟨wR P s, by rw [hr, hw, hp.wr]; simp, by
      have := saved_offset hd hq
      rw [slot_eq]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have ea : ∀ {u : State}, u.gpr .r15 = sb s + BitVec.ofNat 64 (scO P) → ∀ d : Nat,
      u.ea (at_ .r15 d) = sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (d : Int) :=
    fun hu d => by rw [ea_at, hu]
  have sl : ∀ p ∈ saved P, t.mem.readW (sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (p.2 : Int)) 64 =
      s.gpr p.1 := hsl
  rw [restore_eq]
  refine wp_movm (ea h15 _) (hin hrd hwr (.rbx, P.so) (by simp [saved])) fun t₁ u₁ => ?_
  refine wp_movm (ea (by rw [u₁.other _ (by decide), h15]) _)
    (hin (u₁.rd.trans hrd) (u₁.wr.trans hwr) (.rbp, P.so + 8) (by simp [saved])) fun t₂ u₂ => ?_
  refine wp_movm (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h15]) _)
    (hin (u₂.rd.trans (u₁.rd.trans hrd)) (u₂.wr.trans (u₁.wr.trans hwr)) (.r12, P.so + 16) (by simp [saved]))
    fun t₃ u₃ => ?_
  refine wp_movm (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h15]) _)
    (hin (u₃.rd.trans (u₂.rd.trans (u₁.rd.trans hrd))) (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans hwr)))
      (.r13, P.so + 24) (by simp [saved])) fun t₄ u₄ => ?_
  refine wp_movm (ea (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h15]) _)
    (hin (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans (u₁.rd.trans hrd))))
      (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans hwr)))) (.r14, P.so + 32) (by simp [saved]))
    fun t₅ u₅ => ?_
  refine wp_movm (ea (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h15]) _)
    (hin (u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans (u₁.rd.trans hrd)))))
      (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans hwr))))) (.r15, P.so + 40)
      (by simp [saved])) fun t₆ u₆ => WP.block_nil ?_
  have hm : ∀ {u : State}, u.mem = t.mem → ∀ p ∈ saved P,
      u.mem.readW (sb s + BitVec.ofNat 64 (scO P) + BitVec.ofInt 64 (p.2 : Int)) 64 = s.gpr p.1 :=
    fun h p hq => by rw [h]; exact sl p hq
  have m₁ : t₁.mem = t.mem := u₁.mem
  have m₂ : t₂.mem = t.mem := u₂.mem.trans m₁
  have m₃ : t₃.mem = t.mem := u₃.mem.trans m₂
  have m₄ : t₄.mem = t.mem := u₄.mem.trans m₃
  have m₅ : t₅.mem = t.mem := u₅.mem.trans m₄
  refine ⟨fun p hp => ?_, u₆.mem.trans m₅, ?_⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, sl (.rbx, P.so) (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, hm m₁ (.rbp, P.so + 8) (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        hm m₂ (.r12, P.so + 16) (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm m₃ (.r13, P.so + 24) (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, hm m₄ (.r14, P.so + 32) (by simp [saved])]
    · rw [u₆.gpr, hm m₅ (.r15, P.so + 40) (by simp [saved])]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]

theorem ret_stk (s : State) : (retR s).Disjoint (stkR s) := by
  have := Offset.disjoint_base (s.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega_arith)
  rwa [BitVec.sub_add_cancel] at this

theorem finish_ok {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {s t : State} (hp : Pre P D s) (h : Mid P s t)
    (hh : H.lenOk (len s) → H.hash iv (msg s) = H.digest (H.stateAt t.mem (sb s))) :
    WP isa (.block (finish P)) t fun t' => gprPreserved s t' ∧
      (H.lenOk (len s) → bytesAt t'.mem (out s) D = (H.hash iv (msg s)).take D) := by
  have := hF.lt; have := st_le P; have := sc_le P; have := hd.B; have := hd.N; have hD := hs.le
  unfold finish
  rw [WP.block_append_iff, WP.block_append_iff]
  have hsub : Region.Sub (hR P s) (wR P s) := h_sub s
  refine WP.mono (hs.out t ⟨wR P s, by rw [h.rd, h.wr, hp.rd, hp.wr]; simp, by
        rw [h.rbx]
        have := Offset.contains_base (sb s) (d := 0) (n := P.N) (k := scratchBytes P) (by omega) (by omega)
        simpa using this⟩
      ⟨oR s D, by rw [h.wr, hp.wr]; simp, by rw [h.rbp]; exact Region.contains_self _ _⟩
      (by rw [h.rbx, h.rbp]; exact (hp.o_w.sub_right hsub).symm)) fun t₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  rw [h.rbp, h.rbx] at m₁
  unfold wipe
  refine wp_xbin ?_
  refine WP.mono (wipes_ok hF hp ((P.N + P.B + 15) / 16) (by simp only [scO]; omega)
      (by show t₁.gpr .rbx = _; rw [g₁ _ (by decide), h.rbx]) (by show t₁.wr = _; rw [wr₁, h.wr]))
    fun t₂ ⟨g₂, rd₂, wr₂, f₂⟩ => ?_
  have e : (t₁.setXmm .xmm0 (XBinOp.pxor.eval (t₁.xmm .xmm0) (t₁.xmm .xmm0))).mem = t₁.mem := rfl
  rw [e] at f₂
  -- The digest's bytes, and the saved registers, are outside what `wipe` wrote.
  have hdig : ((H.digest (H.stateAt t.mem (sb s))).take D).length = D := by
    rw [List.length_take, H.digest_length]; omega
  have hwo : Region.Disjoint ⟨sb s, scO P⟩ (oR s D) := (hp.o_w.sub_right (Region.sub_prefix (by omega))).symm
  have hsl₂ : Slots P s t₂.mem := fun p hq => by
    rw [← h.slots p hq]
    have f₁ : Frame [oR s D] t.mem t₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdig]; exact Region.contains_self _ _)
    rw [f₂.readW (slot_contains hd s hq) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.base_disjoint _ (by omega) (by omega) : Region.Disjoint ⟨sb s, scO P⟩ (slR P s)).symm)
        (by decide)]
    exact f₁.readW (slot_contains hd s hq) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_w.sub_right (sl_sub s)).symm) (by decide)
  refine WP.mono (restore_ok hF hd hp (by rw [wr₂]; exact (wr₁.trans h.wr))
      (by rw [rd₂]; exact (rd₁.trans h.rd)) (by rw [g₂]; show t₁.gpr .r15 = _; rw [g₁ _ (by decide), h.r15]) hsl₂)
    fun t₃ ⟨g₃, m₃, sp₃⟩ => ⟨⟨fun r hr => ?_, ?_⟩, fun hok => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g₃ (.rbx, P.so) (by simp [saved])
    · exact g₃ (.rbp, P.so + 8) (by simp [saved])
    · rw [sp₃, g₂]; show t₁.gpr .rsp = _; rw [g₁ _ (by decide), h.rsp]
    · exact g₃ (.r12, P.so + 16) (by simp [saved])
    · exact g₃ (.r13, P.so + 24) (by simp [saved])
    · exact g₃ (.r14, P.so + 32) (by simp [saved])
    · exact g₃ (.r15, P.so + 40) (by simp [saved])
  · -- The return address.
    rw [m₃]
    have e₂ : t₂.mem.readW (s.gpr .rsp) 64 = t₁.mem.readW (s.gpr .rsp) 64 :=
      f₂.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_w.sub_right (Region.sub_prefix (by omega))) (by decide)
    have e₁ : t₁.mem.readW (s.gpr .rsp) 64 = t.mem.readW (s.gpr .rsp) 64 := by
      rw [m₁]
      exact (writeBytes_frame _ _ _ (R := oR s D) (by rw [hdig]; exact Region.contains_self _ _)).readW
        (Region.contains_self _ _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_o)
        (by decide)
    rw [e₂, e₁]
    exact h.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.ret_w
      · exact ret_stk s) (by decide)
  · -- The digest.
    rw [m₃, VG.Proof.Sha256.Stream.bytesAt_congr (n := D) (fun i hi => f₂.bytes (R := oR s D)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwo.symm) (by show D ≤ 2 ^ 64; omega) hi),
      m₁, hh hok]
    have := VG.Proof.Sha256.Stream.bytesAt_writeBytes t.mem (out s) 0
      ((H.digest (H.stateAt t.mem (sb s))).take D) (by rw [hdig]; omega)
    rw [hdig, Nat.zero_add, BitVec.add_zero] at this
    rw [this]; simp [bytesAt]

/-! ## The body -/

theorem correct {P : Params} (hF : Fits P) {H : Md P.B P.N P.L} (hd : Dims P) {D : Nat} (hs : ShapeD H D)
    {iv : H.HV} {init : Prog isa}
    (hi : ∀ s, (initK H iv).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (initK H iv).post s s')
    (hiw : ∀ r, r ≠ .rax → ∀ i ∈ instrs init, Taint.clobbers i r = false) (hin : init.noCalls = true)
    {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State} (hp : Pre P D s) :
    WP isa (body P init name code) s fun s' => gprPreserved s s' ∧ (oneK H iv D).post s s' := by
  unfold body
  refine WP.seq (WP.mono (setup_ok hF hd hp) fun t₁ ⟨m₁, h13₁, hdi₁⟩ => ?_)
  refine WP.seq (WP.mono (init_ok hF hd hi hiw hin hp m₁ h13₁ hdi₁) fun t₂ ⟨m₂, h13₂, hiv₂⟩ => ?_)
  refine WP.seq (WP.mono (whole_ok hF hd hf hp m₂ h13₂ hiv₂) fun t₃ ⟨m₃, h13₃, hw₃⟩ => ?_)
  refine WP.seq (WP.mono (tail_ok hF hd hs hf hp m₃ h13₃ hw₃) fun t₄ ⟨m₄, hh₄⟩ => ?_)
  exact WP.mono (finish_ok hF hd hs hp m₄ hh₄) fun t₅ ⟨g₅, h₅⟩ => ⟨g₅, h₅⟩

/-! ## Facts about every instruction

`body`'s instructions are those of `init` and of the body without it, so a
fact checked by evaluating the code is checked once without `init`. -/

theorem body_allInstrs (P : Params) (init : Prog isa) (name : String) (code : Prog isa) (p : Instr → Bool) :
    (body P init name code).allInstrs p = ((body P (.block []) name code).allInstrs p && init.allInstrs p) := by
  simp only [body, Code.allInstrs]
  cases init.allInstrs p <;> simp

theorem body_all (P : Params) (init : Prog isa) (name : String) (code : Prog isa) (p : Instr → Bool) :
    (body P init name code).all p = ((body P (.block []) name code).all p && init.all p) := by
  simp only [body, Code.all]
  cases init.all p <;> simp

theorem body_depth (P : Params) {init : Prog isa} (h : init.x86_64Depth = 0) (name : String) (code : Prog isa) :
    (body P init name code).x86_64Depth = (body P (.block []) name code).x86_64Depth := by
  simp only [body, Code.x86_64Depth, h]

end VG.Proof.MdStream.X86_64.OneShot
