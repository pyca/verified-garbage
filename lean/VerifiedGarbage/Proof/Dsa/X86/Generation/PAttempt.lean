module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
import VerifiedGarbage.Proof.Rsa.X86.DivLoop
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd

/-! ### `Dsa.X86.Generation.AddBE`, which this module and modules that import it used -/

section

/-! # The big-endian addition of a word to bytes of `scratch`

`addBE n` adds `ecx` to the `n` bytes ending at `edx`, big-endian, modulo
`2^(8 n)`: the counter's offset added to the seed (FIPS 186-4 A.1.1.2). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Dsa.X86.Generation (addBE addStep)
open VG.Proof.Dsa.Generation

theorem off_add_ofNat (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem setWidth8_ofNat (x : Nat) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd x (by decide)

theorem getElem?_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n)[i]? = some (m (p + BitVec.ofNat 64 i)) := by
  simp [Spec.Rsa.bytesAt, hi]

section
variable {is : List Instr} {s : State} {Q : State → Prop} {base : Addr} {size : Nat}

/-- `movzx eax, byte [edx]`, `edx` at `scratch + d`. -/
theorem ldx_ok {d : Nat} (hs : Scr s base size) (hd : d + 1 ≤ size)
    (he : s.gpr .edx = s.gpr .edi + BitVec.ofNat 32 d)
    (k : ∀ s', Upd s s' .eax ((s.mem (off base d)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 .eax (at_ .edx 0) :: is)) s Q := by
  obtain e : VG.X86.addr (s.gpr .edx) 0 = off base d := by
    simp only [VG.X86.addr, he, BitVec.add_zero]; exact Scr.wide hs (by omega_using [hd])
  refine cons (s' := s.setReg .eax ((s.mem (off base d)).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  obtain hin := hs.read (d := d) (n := 1) hd
  simp only [exec, State.load8, at_, ea_mk, e, hin, ↓reduceIte, Option.map_some]

/-- `mov byte [edx], al`, `edx` at `scratch + d`. -/
theorem stx_ok {d : Nat} (hs : Scr s base size) (hd : d + 1 ≤ size)
    (he : s.gpr .edx = s.gpr .edi + BitVec.ofNat 32 d)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) ((s.gpr .eax).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .edx 0) .al :: is)) s Q := by
  obtain e : VG.X86.addr (s.gpr .edx) 0 = off base d := by
    simp only [VG.X86.addr, he, BitVec.add_zero]; exact Scr.wide hs (by omega_using [hd])
  refine cons (s' := { s with mem := s.mem.writeW (off base d) ((s.gpr .eax).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  obtain hout := hs.write (d := d) (n := 1) hd
  simp only [exec, State.store8, at_, ea_mk, e, hout, ↓reduceIte, Reg8.reg]

end

/-- What remains of the loop with `m + 1` bytes left: the bytes below them
are the seed's, those above them the result's, and `c` the carry. -/
structure AddInv (s : State) (base : Addr) (size o n c : Nat) (m : Nat) (t : State) : Prop where
  le : m + 1 ≤ n
  esi : t.gpr .esi = BitVec.ofNat 32 (m + 1)
  edx : t.gpr .edx = t.gpr .edi + BitVec.ofNat 32 (o + m)
  carry : ∃ c', t.gpr .ecx = BitVec.ofNat 32 c' ∧ c' + 256 ≤ 2 ^ 32 ∧
    (Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base o) n) + c)).take (m + 1) =
      Spec.Dsa.encodeBE (m + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s.mem (off base o) n).take (m + 1)) + c')
  low : ∀ i ≤ m, t.mem (off base (o + i)) = s.mem (off base (o + i))
  high : ∀ i, m < i → i < n → t.mem (off base (o + i)) =
    (Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base o) n) + c)).getD i 0
  frame : Frame [⟨off base o, n⟩] s.mem t.mem
  keeps : Keeps [.eax, .ecx, .edx, .esi] s t
  syms : t.syms = s.syms

/-- One byte: the byte with the carry, and the carry on. -/
theorem addStep_ok {s : State} {base : Addr} {size o n c m : Nat} (hs : Scr s base size)
    (ho : o + n ≤ size) {t : State} (I : AddInv s base size o n c m t) :
    WP isa (.block addStep) t fun t' => t'.zf = some (decide (m = 0)) ∧
      (m = 0 → Spec.Rsa.bytesAt t'.mem (off base o) n =
          Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base o) n) + c) ∧
        Frame [⟨off base o, n⟩] s.mem t'.mem ∧ Keeps [.eax, .ecx, .edx, .esi] s t' ∧ t'.syms = s.syms) ∧
      (∀ m', m = m' + 1 → AddInv s base size o n c m' t') := by
  obtain ⟨hle, hesi, hedx, ⟨c', hc, hcb, htake⟩, hlow, hhigh, hfr, hk, hsy⟩ := I
  have nw := hs.nowrap
  have sl := hs.size_lt
  obtain ht : Scr t base size := Scr.of_eq hs (hk.1 _ (by decide)) (hk.1 _ (by decide)) hk.2.2
  obtain hbt := hlow m (Nat.le_refl _)
  obtain hBm : (Spec.Rsa.bytesAt s.mem (off base o) n).take (m + 1) =
      (Spec.Rsa.bytesAt s.mem (off base o) n).take m ++ [s.mem (off base (o + m))] := by
    rw [List.take_add_one, getElem?_bytesAt _ _ (by omega_arith), off_add_ofNat]; rfl
  obtain hBl := VG.Proof.Bignum.bytesAt_length s.mem (off base o) n
  generalize hB : Spec.Rsa.bytesAt s.mem (off base o) n = B at htake hhigh hBm hBl ⊢
  generalize hR : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE B + c) = R at htake hhigh ⊢
  obtain hRl : R.length = n := by rw [← hR, encodeBE_length]
  generalize s.mem (off base (o + m)) = b at hbt hBm
  have hbn := b.isLt
  obtain hsum : b.toNat + c' < 2 ^ 32 := by omega_arith
  -- The step's result.
  obtain hR1 : R.take (m + 1) = Spec.Dsa.encodeBE m (Spec.Dsa.decodeBE (B.take m) + (b.toNat + c') / 256) ++
      [BitVec.ofNat 8 (b.toNat + c')] := by
    obtain h := seedAdd_snoc (B.take m) b c'
    rw [List.length_take, Nat.min_eq_left (by omega_arith)] at h
    rw [htake, hBm, h]
  obtain hRm : R.take m = Spec.Dsa.encodeBE m (Spec.Dsa.decodeBE (B.take m) + (b.toNat + c') / 256) := by
    rw [show R.take m = (R.take (m + 1)).take m by rw [List.take_take, Nat.min_eq_left (by omega_arith)], hR1,
      List.take_left' (encodeBE_length _ _)]
  obtain hRg : R.getD m 0 = BitVec.ofNat 8 (b.toNat + c') := by
    rw [show R.getD m 0 = (R.take (m + 1)).getD m 0 by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, show m < m + 1 by omega_arith, ↓reduceIte], hR1,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [encodeBE_length]), encodeBE_length,
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  -- The instructions.
  simp only [addStep]
  refine ldx_ok ht (d := o + m) (by omega_arith) hedx fun s₁ u₁ => wp_add fun s₂ u₂ _ => ?_
  obtain di₂ : s₂.gpr .edi = t.gpr .edi := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain dx₂ : s₂.gpr .edx = t.gpr .edx := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain ax₂ : s₂.gpr .eax = BitVec.ofNat 32 (b.toNat + c') := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hc, hbt]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_arith), Nat.mod_eq_of_lt (a := c') (by omega_arith)]
  obtain ht₂ : Scr s₂ base size := Scr.of_eq ht di₂ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.wr, u₁.wr])
  refine stx_ok ht₂ (d := o + m) (by omega_arith) (by rw [dx₂, di₂, hedx]) fun s₃ M₃ =>
    wp_shr (n := 8) (by decide) fun s₄ u₄ _ => wp_mov fun s₅ u₅ => wp_subi fun s₆ u₆ _ _ =>
    wp_subi fun s₇ u₇ _ _ => wp_cmpi fun s₈ f₈ _ z₈ => WP.block_nil ?_
  obtain g₈ : ∀ r, r ∉ [.eax, .ecx, .edx, .esi] → s₈.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₈.gpr, u₇.other r hr.2.2.2, u₆.other r hr.2.2.1, u₅.other r hr.2.1, u₄.other r hr.1, M₃.gpr,
      u₂.other r hr.1, u₁.other r hr.1]
  obtain di₈ : s₈.gpr .edi = t.gpr .edi := g₈ _ (by decide)
  obtain m₈ : s₈.mem = t.mem.writeW (off base (o + m)) (BitVec.ofNat 8 (b.toNat + c')) := by
    rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, M₃.mem, ax₂, setWidth8_ofNat, u₂.mem, u₁.mem]
  obtain cx₈ : s₈.gpr .ecx = BitVec.ofNat 32 ((b.toNat + c') / 256) := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, M₃.gpr, ax₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (a := b.toNat + c') (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain dx₈ : s₈.gpr .edx = t.gpr .edx - 1 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), M₃.gpr, dx₂]
  obtain si₈ : s₈.gpr .esi = BitVec.ofNat 32 m := by
    rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), M₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hesi]
    exact ofNat_pred (k := m + 1) (by omega_arith)
  obtain zf₈ : s₈.zf = some (decide (m = 0)) := by
    rw [z₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), M₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hesi, ofNat_pred (k := m + 1) (by omega_arith),
      Nat.add_sub_cancel]
    exact congrArg some (sub_beq (b := 0) (by omega_arith) (by decide))
  obtain rd₈ : s₈.rd = s.rd := by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, M₃.rd, u₂.rd, u₁.rd, hk.2.1]
  obtain wr₈ : s₈.wr = s.wr := by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, M₃.wr, u₂.wr, u₁.wr, hk.2.2]
  obtain sy₈ : s₈.syms = s.syms := by
    rw [f₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, M₃.syms, u₂.syms, u₁.syms, hsy]
  obtain k₈ : Keeps [.eax, .ecx, .edx, .esi] s s₈ :=
    ⟨fun r hr => (g₈ r hr).trans (hk.1 r hr), rd₈, wr₈⟩
  obtain ne_m : ∀ i, i < n → i ≠ m → off base (o + i) ≠ off base (o + m) := fun i hi h =>
    Offset.add_ofNat_ne base (by omega_arith) (by omega_arith) (by omega_arith)
  obtain fr₈ : Frame [⟨off base o, n⟩] s.mem s₈.mem := fun x hx => by
    obtain hin : (⟨off base o, n⟩ : Region).Contains (off base (o + m)) 1 := by
      rw [← off_add_ofNat]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    obtain hne : x ≠ off base (o + m) := fun h => hx _ (List.mem_singleton_self _) (h ▸ hin)
    rw [m₈, WriteBytes.writeW8_apply, ite_eq_right_iff.mpr (fun h => absurd h hne), hfr x hx]
  refine ⟨zf₈, fun h0 => ⟨?_, fr₈, k₈, sy₈⟩, fun m' hm' => ⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, fr₈, k₈, sy₈⟩⟩
  · -- The last byte: the result.
    subst h0
    apply List.ext_getElem (by rw [VG.Proof.Bignum.bytesAt_length, hRl])
    intro i hi hi'
    rw [VG.Proof.Bignum.bytesAt_length] at hi
    rw [show R[i] = R.getD i 0 by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [off_add_ofNat, m₈, WriteBytes.writeW8_apply]
    by_cases hi0 : i = 0
    · subst hi0; simp only [Nat.add_zero, ↓reduceIte, hRg]
    · simp only [ne_m i hi hi0, ↓reduceIte, hhigh i (by omega_arith) hi]
  · rw [si₈, hm']
  · rw [dx₈, di₈, hedx, hm', show o + (m' + 1) = (o + m') + 1 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · refine ⟨(b.toNat + c') / 256, cx₈, by omega_arith, ?_⟩
    subst hm'
    rw [hB, hR, hRm]
  · intro i hi
    rw [m₈, WriteBytes.writeW8_apply]
    simp only [ne_m i (by omega_arith) (by omega_arith), ↓reduceIte, hlow i (by omega_arith)]
  · intro i hi hin
    rw [m₈, WriteBytes.writeW8_apply, hB, hR]
    by_cases him : i = m
    · subst him; simp only [↓reduceIte, hRg]
    · simp only [ne_m i hin him, ↓reduceIte, hhigh i (by omega_arith) hin]

/-- `addBE n` adds `ecx` to the `n` bytes at `scratch + o`, big-endian,
modulo `2^(8 n)`. -/
theorem addBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o n c : Nat} (hn : 0 < n)
    (ho : o + n ≤ size) (hc : c + 256 ≤ 2 ^ 32)
    (hedx : s.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (o + n - 1)) (hecx : s.gpr .ecx = BitVec.ofNat 32 c) :
    WP isa (addBE n) s fun t => Spec.Rsa.bytesAt t.mem (off base o) n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base o) n) + c) ∧
      Frame [⟨off base o, n⟩] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .esi] s t ∧ t.syms = s.syms := by
  have sl := hs.size_lt
  unfold addBE
  refine WP.seq (wp_movi fun s₀ u₀ => WP.block_nil ?_)
  refine WP.loop (M := isa) (AddInv s base size o n c)
    (fun m t I => WP.mono (addStep_ok hs ho I) fun t' ⟨hz, hf, hk⟩ => ?_) (n - 1) s₀ ?_
  · by_cases h0 : m = 0
    · exact .inl ⟨by simp [X86.eval, hz, h0], hf h0⟩
    · exact .inr ⟨by simp [X86.eval, hz, h0], m - 1, by omega_using [h0], hk (m - 1) (by omega_using [h0])⟩
  · have hBl := VG.Proof.Bignum.bytesAt_length s.mem (off base o) n
    refine ⟨by omega_using [hn], ?_, ?_, ⟨c, ?_, hc, ?_⟩, fun i _ => by rw [u₀.mem], fun i hi hi' => by omega,
      fun x _ => by rw [u₀.mem], ⟨fun r hr => u₀.other r fun h => hr (by simp [h]), u₀.rd, u₀.wr⟩, u₀.syms⟩
    · rw [u₀.gpr, Nat.sub_add_cancel hn]
    · rw [u₀.other _ (by decide), u₀.other _ (by decide), hedx, Nat.add_sub_assoc hn]
    · rw [u₀.other _ (by decide), hecx]
    · rw [Nat.sub_add_cancel hn, List.take_of_length_le (by rw [encodeBE_length]),
        List.take_of_length_le (by omega_using [hBl])]

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.Flags`, which this module and modules that import it used -/

section

/-! # The search's state words: compared with constants, and set -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation (cmpF stImm)

section
variable {is : List Instr} {s : State} {Q : State → Prop} {base : Addr} {size : Nat}

/-- The word at `o`, `w`, compared with `v`: ZF is `w = v`. -/
theorem cmpF_ok {o v w : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (hw : s.mem.readW (off base o) 32 = BitVec.ofNat 32 w) (hwl : w < 2 ^ 32) (hv : v < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → isa.eval .e s' = some (decide (w = v)) → WP isa (.block is) s' Q) :
    WP isa (.block (cmpF o v ++ is)) s Q := by
  simp only [cmpF, List.cons_append, List.nil_append]
  refine ld_ok hs ho fun s₁ u₁ => wp_cmpi fun s₂ f₂ _ z₂ => k s₂ (fun r hr => by rw [f₂.gpr, u₁.other r hr])
    (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms]) ?_
  show s₂.zf = _
  rw [z₂, u₁.gpr, hw, sub_beq hwl hv]

/-- The word at `o` := `v`. -/
theorem stImm_ok {o v : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (off base o) (BitVec.ofNat 32 v) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (stImm o v ++ is)) s Q := by
  simp only [stImm, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => st_ok (Scr.of_eq hs (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) ho
    fun s₂ M₂ => k s₂ (fun r hr => by rw [M₂.gpr, u₁.other r hr]) (by rw [M₂.mem, u₁.mem, u₁.gpr])
      (by rw [M₂.rd, u₁.rd]) (by rw [M₂.wr, u₁.wr]) (by rw [M₂.syms, u₁.syms])

/-- `cmpF` ending a block. -/
theorem cmpF_end {o v w : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (hw : s.mem.readW (off base o) 32 = BitVec.ofNat 32 w) (hwl : w < 2 ^ 32) (hv : v < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → isa.eval .e s' = some (decide (w = v)) → Q s') :
    WP isa (.block (cmpF o v)) s Q := by
  rw [← List.append_nil (cmpF o v)]
  exact cmpF_ok hs ho hw hwl hv fun s' a b c d e f => WP.block_nil (k s' a b c d e f)

/-- `stImm` ending a block. -/
theorem stImm_end {o v : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (off base o) (BitVec.ofNat 32 v) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Q s') :
    WP isa (.block (stImm o v)) s Q := by
  rw [← List.append_nil (stImm o v)]
  exact stImm_ok hs ho fun s' a b c d e => WP.block_nil (k s' a b c d e)

/-- The word at `o`, `w`, compared with `v`: CF is `w < v`. -/
theorem cmpFb_ok {o v w : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (hw : s.mem.readW (off base o) 32 = BitVec.ofNat 32 w) (hwl : w < 2 ^ 32) (hv : v < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → isa.eval .b s' = some (decide (w < v)) → WP isa (.block is) s' Q) :
    WP isa (.block (cmpF o v ++ is)) s Q := by
  simp only [cmpF, List.cons_append, List.nil_append]
  refine ld_ok hs ho fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => k s₂ (fun r hr => by rw [f₂.gpr, u₁.other r hr])
    (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms]) ?_
  show s₂.cf = _
  rw [c₂, u₁.gpr, hw, toNat_ofNat_lt hwl, toNat_ofNat_lt hv]

/-- `cmpF`, for CF, ending a block. -/
theorem cmpFb_end {o v w : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (hw : s.mem.readW (off base o) 32 = BitVec.ofNat 32 w) (hwl : w < 2 ^ 32) (hv : v < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → isa.eval .b s' = some (decide (w < v)) → Q s') :
    WP isa (.block (cmpF o v)) s Q := by
  rw [← List.append_nil (cmpF o v)]
  exact cmpFb_ok hs ho hw hwl hv fun s' a b c d e f => WP.block_nil (k s' a b c d e f)

end

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.LoadStore`, which this module and modules that import it used -/

section

/-! # Big-endian bytes of `scratch` into arrays of 32-bit words, and back -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation (loadS storeS)

/-- The `len` big-endian bytes at `scratch + src` into the `2 k` words at
`scratch + o`. -/
theorem loadS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k o src len : Nat}
    (hk : 0 < k) (ho : o + 8 * k ≤ size) (hl : 0 < len) (hlen : len ≤ 8 * k) (hsrc : src + len ≤ size)
    (hsep : src + len ≤ o ∨ o + 8 * k ≤ src) :
    WP isa (loadS k o src len) s fun t =>
      val32 t.mem base o (2 * k) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base src) len) ∧
      Outside base o (8 * k) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold loadS
  refine WP.seq (scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => wp_movi fun s₂ u₂ => WP.block_nil ?_)
  have hs₂ : Scr s₂ base size := Scr.of_eq hs (by rw [u₂.other _ (by decide), g₁ _ (by decide)])
    (by rw [u₂.other _ (by decide), g₁ _ (by decide)]) (by rw [u₂.wr, wr₁])
  have esi₂ : s₂.gpr .esi = s.gpr .edi + BitVec.ofNat 32 src := by rw [u₂.other _ (by decide), e₁]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have srcW := Scr.wide hs (d := src) (by omega_using [hl, hsrc])
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₂ :=
    ⟨fun r hr => by rw [u₂.other r (by simp_all), g₁ r (by simp_all)], by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  refine WP.mono (VG.Proof.Bignum.X86.loadBE_ok hs₂ hk ho hl hlen
    (by rw [esi₂, Scr.toNat_add hs (by omega_using [hl, hsrc])]; omega_using [hsrc, nw]) u₂.gpr
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, srcW, u₂.rd, u₂.wr, rd₁, wr₁]; exact hs.read hsrc)
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, srcW]
        exact Offset.disjoint base (by omega_using [hsep]) (by omega_using [hsrc, nw]) (by omega_using [ho, nw]))) fun t ⟨V, O, K⟩ => ?_
  rw [esi₂, VG.Proof.Bignum.X86.byteAddr, srcW, m₂, wordsVal_eq_val32] at V
  rw [m₂] at O
  exact ⟨by rw [V, decodeBE_os2ip], O, K₂.trans K⟩

/-- The `2 n` words at `scratch + o`, as `len` big-endian bytes at
`scratch + dst`. -/
theorem storeS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o dst len n : Nat}
    (hl : 0 < len) (hlen : len ≤ 8 * n) (ho : o + 8 * n ≤ size) (hd : dst + len ≤ size)
    (hsep : o + len ≤ dst ∨ dst + len ≤ o) (fit : val32 s.mem base o (2 * n) < 2 ^ (8 * len)) :
    WP isa (storeS o dst len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base dst) len = Spec.Dsa.encodeBE len (val32 s.mem base o (2 * n)) ∧
      Frame [⟨off base dst, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold storeS
  refine WP.seq (scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => wp_movi fun s₂ u₂ => WP.block_nil ?_)
  have hs₂ : Scr s₂ base size := Scr.of_eq hs (by rw [u₂.other _ (by decide), g₁ _ (by decide)])
    (by rw [u₂.other _ (by decide), g₁ _ (by decide)]) (by rw [u₂.wr, wr₁])
  have ebx₂ : s₂.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 dst := by rw [u₂.other _ (by decide), e₁]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have dstW := Scr.wide hs (d := dst) (by omega_using [hl, hd])
  have K₂ : Keeps [.eax, .ebx, .esi, .ecx] s s₂ :=
    ⟨fun r hr => by rw [u₂.other r (by simp_all), g₁ r (by simp_all)], by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  refine WP.mono (VG.Proof.Bignum.X86.storeBE_ok hs₂ (n := n) hl hlen ho u₂.gpr
    (by rw [m₂, wordsVal_eq_val32]; exact fit)
    (by rw [ebx₂, Scr.toNat_add hs (by omega_using [hl, hd])]; omega_using [hd, nw])
    (by rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW, u₂.wr, wr₁]; exact hs.write hd)
    (by rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW]
        exact Offset.disjoint base (by omega_using [hsep]) (by omega_using [hlen, ho, nw]) (by omega_using [hd, nw]))) fun t ⟨V, F, K⟩ => ?_
  rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW, m₂, wordsVal_eq_val32] at V
  rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW, m₂] at F
  exact ⟨by rw [V, encodeBE_i2osp], F, K₂.trans K⟩

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.PX`, which only this module used -/

section

/-! ### `Dsa.X86.Generation.PHash`, which only this module used -/

section

/-! # One hash of p's candidate

The hash of `seed + offset + j` (A.1.1.2 step 11.1), into its place in `X`:
the `j`-th `qLen` bytes from `X`'s end. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Where hash `j` goes. -/
def hashAt (g : Geo) (j : Nat) : Nat := sX + g.pLen - (j + 1) * g.qLen

/-- The ranges p's hashes change: the block, the hash's scratch and `X`
with the bytes below it the last hash spills into. -/
def pxRanges (g : Geo) : List (Nat × Nat) := [(sState, sX + g.pLen - sState)]

/-- The digest of `seed + offset + j`. -/
def pDig (g : Geo) (seed : List Byte) (offset j : Nat) : List Byte :=
  Spec.Dsa.seedHash (8 * g.qLen) (Spec.Dsa.encodeBE g.qLen (Spec.Dsa.decodeBE seed + offset + j))

/-- The ranges hash `j` changes. -/
def hRanges (g : Geo) (j : Nat) : List (Nat × Nat) := [(sState, 128), (sHScr, 560), (hashAt g j, g.qLen)]

theorem pxRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (pxRanges g) := by
  have sz := v.size_ge
  have b := G.bounds
  intro o ho
  simp only [pxRanges, List.mem_singleton] at ho; subst ho
  simp only [sState, sX, fOut, fWitLen, hdr]; omega_using [sz, b]

theorem hRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {j : Nat} (hj : j ≤ g.count) :
    E.Apart (hRanges g j) := by
  have sz := v.size_ge
  have b := G.bounds
  obtain hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_using [hj])
  intro o ho
  simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOut, fWitLen, hdr] <;> omega_arith

theorem pHash_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {offset j : Nat} (hO : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset)
    (hoj : offset + j + 256 ≤ 2 ^ 32) (hj : j ≤ g.count) :
    WP isa (g.pHash j) s fun t => Base E t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (hashAt g j)) g.qLen = pDig g (chunk E k) offset j ∧
      E.Chg (hRanges g j) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have sz := v.size_ge
  have nl := G.hash.N_le
  have bd := G.bounds
  have hN := G.N
  obtain hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
  obtain Ap := hRanges_apart G v hj
  unfold Geo.pHash
  simp only [seqs]
  refine WP.seq (VG.X86.WP.mono_syms (seedIn_ok G v hq B hk hS) fun t₁ ⟨S₁, F₁, K₁⟩ sy₁ => ?_)
  obtain C₁ : E.Chg (hRanges g j) s.mem t₁.mem := Env.Chg.of_frame F₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega_arith) (by simp only [sState]; omega_arith)
  obtain B₁ : Base E t₁ := B.keep v C₁ Ap (K₁.1 _ (by decide)) (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 sy₁
  obtain hO₁ : t₁.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset := by
    rw [Env.Chg.word v C₁ (by simp only [fOffset, hdr]; omega_arith) (fun o ho => ⟨(Ap o ho).1, by
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX, fOffset, hdr] <;> omega_arith⟩), hO]
  refine WP.seq (scr_ok fun t₂ e₂ g₂ m₂ rd₂ wr₂ sy₂ =>
    ld_ok (Scr.of_eq B₁.scr (g₂ _ (by decide)) (g₂ _ (by decide)) wr₂) (d := fOffset)
      (by simp only [fOffset, hdr]; omega_arith) fun t₃ u₃ => wp_addi fun t₄ u₄ => WP.block_nil ?_)
  obtain edi₄ : t₄.gpr .edi = t₁.gpr .edi := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
  obtain esp₄ : t₄.gpr .esp = t₁.gpr .esp := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
  obtain m₄ : t₄.mem = t₁.mem := by rw [u₄.mem, u₃.mem, m₂]
  obtain hs₄ : Scr t₄ E.base E.size := Scr.of_eq B₁.scr edi₄ esp₄ (by rw [u₄.wr, u₃.wr, wr₂])
  obtain edx₄ : t₄.gpr .edx = t₄.gpr .edi + BitVec.ofNat 32 (sState + g.H.N + g.qLen - 1) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂, edi₄]
  obtain ecx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (offset + j) := by
    rw [u₄.gpr, u₃.gpr, m₂, hO₁, BitVec.ofNat_add]
  refine WP.seq (VG.X86.WP.mono_syms (addBE_ok hs₄ (o := sState + g.H.N) (n := g.qLen) (c := offset + j)
    (by omega_arith) (by simp only [sState]; omega_arith) hoj (by rw [edx₄]) ecx₄) fun t₅ ⟨S₅, F₅, K₅, _⟩ sy₅ => ?_)
  rw [m₄, S₁] at S₅
  obtain C₅ : E.Chg (hRanges g j) s.mem t₅.mem := C₁.trans (Env.Chg.of_frame (m₄ ▸ F₅) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega_arith) (by simp only [sState]; omega_arith))
  obtain rd₅ : t₅.rd = s.rd := by rw [K₅.2.1, u₄.rd, u₃.rd, rd₂, K₁.2.1]
  obtain wr₅ : t₅.wr = s.wr := by rw [K₅.2.2, u₄.wr, u₃.wr, wr₂, K₁.2.2]
  obtain sy₅s : t₅.syms = s.syms := by rw [sy₅, u₄.syms, u₃.syms, sy₂, sy₁]
  obtain edi₅ : t₅.gpr .edi = s.gpr .edi := by rw [K₅.1 _ (by decide), edi₄, K₁.1 _ (by decide)]
  obtain esp₅ : t₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), esp₄, K₁.1 _ (by decide)]
  obtain B₅ : Base E t₅ := B.keep v C₅ Ap edi₅ esp₅ rd₅ wr₅ sy₅s
  have sp₅ : t₅.gpr .esp = E.sp := B₅.sp
  have low := v.low
  obtain stk₅ : Region.Sub (VG.Proof.Pbkdf2.Stream.X86.stk t₅) E.stackRegion := by
    simp only [VG.Proof.Pbkdf2.Stream.X86.stk, sp₅, Env.stackRegion]; exact below_sub (by decide) (by omega_arith)
  have so := G.hash.ok.sizes.so
  have sW := G.hash.ok.sizes.W
  have hd : sX + g.pLen - (j + 1) * g.qLen = hashAt g j := rfl
  rw [hd, ← hN]
  refine VG.X86.WP.mono_syms (hash_ok G.hash B₅.scr (dst := hashAt g j)
    (by simp only [sHScr]; omega_arith) (by simp only [sHScr]; omega_arith) (by simp only [hashAt, sX]; omega_arith)
    (by simp only [hashAt, sState, sX]; omega_arith) (by simp only [hashAt, sHScr, sX]; omega_arith) (by rw [sp₅]; omega_arith)
    (v.scratchStack.symm.sub_left stk₅)) fun t₆ ⟨H₆, F₆, G₆, rd₆, wr₆⟩ sy₆ => ?_
  obtain bsEq : ∀ m p n, Spec.Sha256.bytesAt m p n = Spec.Rsa.bytesAt m p n := fun _ _ _ => rfl
  simp only [bsEq] at H₆
  rw [← hN] at S₅
  rw [S₅, G.seedHash] at H₆
  obtain C₆ : E.Chg (hRanges g j) s.mem t₆.mem := C₅.trans (Env.Chg.of_frame F₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Env.in_range (o := (sState, 128)) (by simp [hRanges]) (by omega_arith) (by omega_arith)
    · exact Env.in_range (o := (sHScr, 560)) (by simp [hRanges]) (by omega_arith) (by omega_arith)
    · exact Env.in_range (o := (hashAt g j, g.qLen)) (by simp [hRanges]) (by omega_arith) (by omega_arith)
    · exact Env.in_stack stk₅)
  obtain edi₆ : t₆.gpr .edi = s.gpr .edi := by
    rw [G₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), edi₅]
  obtain esp₆ : t₆.gpr .esp = s.gpr .esp := by
    rw [G₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), esp₅]
  refine ⟨B.keep v C₆ Ap edi₆ esp₆ (by rw [rd₆, rd₅]) (by rw [wr₆, wr₅]) (by rw [sy₆, sy₅s]), ?_, C₆,
    by rw [rd₆, rd₅], by rw [wr₆, wr₅], by rw [sy₆, sy₅s]⟩
  rw [hN] at H₆ ⊢
  rw [H₆, pDig, Nat.add_assoc]

end VG.Proof.Dsa.X86.Generation

end

end

/-! # p's `X`: the hashes, shaped (A.1.1.2 steps 11.1–11.3) -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Generation/Seqs.lean`, which only this module imported.
section

/-! # Composing the generator's sequences of stages -/

section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

theorem seqs_cons_iff (c : Prog isa) (cs : List (Prog isa)) (s : State) (Q : State → Prop) :
    WP isa (seqs (c :: cs)) s Q ↔ WP isa c s (fun t => WP isa (seqs cs) t Q) := by
  cases cs with
  | nil => simp only [seqs, WP.block_nil_iff (M := isa)]
  | cons d ds => exact WP.seq_iff

theorem seqs_append_iff (cs ds : List (Prog isa)) (s : State) (Q : State → Prop) :
    WP isa (seqs (cs ++ ds)) s Q ↔ WP isa (seqs cs) s (fun t => WP isa (seqs ds) t Q) := by
  induction cs generalizing s Q with
  | nil => simp only [List.nil_append, seqs, WP.block_nil_iff (M := isa)]
  | cons c cs ih => simp only [List.cons_append, seqs_cons_iff, ih]

theorem seqs_range_ok (n : Nat) (code : Nat → Prog isa) (P : Nat → State → Prop)
    (step : ∀ j < n, ∀ s, P j s → WP isa (code j) s (P (j + 1)))
    (s : State) (initial : P 0 s) : WP isa (seqs ((List.range n).map code)) s (P n) := by
  induction n generalizing s with
  | zero => exact WP.block_nil initial
  | succ n ih =>
    rw [List.range_succ, List.map_append, seqs_append_iff]
    refine WP.mono (ih (fun j hj => step j (by omega)) s initial) fun t Pt => ?_
    exact step n (by omega) t Pt

end VG.Proof.Dsa.X86.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Dsa.Generation

/-- `c + 1` digits of `q` bytes ending at `T`, the most significant first,
are their radix-`2^(8 q)` sum. -/
theorem digits_value (m : Mem) (p : Addr) (T q : Nat) (v : Nat → Nat) (c : Nat) (hc : (c + 1) * q ≤ T)
    (hv : ∀ j ≤ c, Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off p (T - (j + 1) * q)) q) = v j) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off p (T - (c + 1) * q)) ((c + 1) * q)) =
      contributions (8 * q) v (c + 1) := by
  induction c with
  | zero =>
    rw [contributions_succ, contributions_zero, ← hv 0 (Nat.le_refl _)]
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
  | succ c ih =>
    obtain e₁ : (c + 1 + 1) * q = q + (c + 1) * q := by rw [Nat.succ_mul, Nat.add_comm]
    obtain e₂ : T - (c + 1 + 1) * q + q = T - (c + 1) * q := by rw [e₁] at hc ⊢; omega_using [hc]
    obtain ho : VG.Proof.Bignum.off (off p (T - (q + (c + 1) * q))) q = off p (T - (q + (c + 1) * q) + q) :=
      off_add_ofNat p _ q
    rw [e₁, bytesAt_append, ho, ← e₁, e₂, e₁, decodeBE_append, VG.Proof.Bignum.bytesAt_length,
      ih (by rw [e₁] at hc; omega_using [hc]) (fun j hj => hv j (by omega_using [hj])), ← e₁, hv (c + 1) (Nat.le_refl _),
      contributions_succ (k := c + 1), Nat.add_comm (v (c + 1) * _)]
    congr 2
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, Nat.mul_comm 8, Nat.mul_assoc, Nat.mul_comm q 8]

/-- Seed `k` is `qLen` bytes. -/
theorem chunk_length {E : Env} (v : E.Valid) {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen) :
    (chunk E k).length = E.qLen := by
  obtain hl : E.seedT.length = E.seedsLen := by rw [← B.seeds v, VG.Proof.Bignum.bytesAt_length]
  rw [Nat.succ_mul] at hk
  simp only [chunk, List.length_take, List.length_drop, hl]
  omega_using [hk]

/-- After `X`: its value, A.1.1.2's shaped hashes. -/
structure XPost (E : Env) (g : Geo) (k offset : Nat) (s t : State) : Prop where
  base : Base E t
  x : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base sX) g.pLen) =
    Spec.Ffdh.candidateOf (8 * g.pLen)
      (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1))
  chg : E.Chg (pxRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem pX_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {offset : Nat} (hO : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset)
    (hoff : offset + g.count + 256 ≤ 2 ^ 32) :
    WP isa g.pX s (XPost E g k offset s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  obtain Apx := pxRanges_apart G v
  obtain hcq : (g.count + 1) * g.qLen ≤ sX + g.pLen := by simp only [sX]; omega_arith
  unfold Geo.pX
  rw [seqs_append_iff]
  refine WP.mono (seqs_range_ok (g.count + 1) g.pHash (fun i t => Base E t ∧
      (∀ j < i, Spec.Rsa.bytesAt t.mem (off E.base (hashAt g j)) g.qLen = pDig g (chunk E k) offset j) ∧
      E.Chg (pxRanges g) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms)
    (fun j hj t ⟨Bt, Ht, Ct, rdt, wrt, syt⟩ => ?_) s
    ⟨B, fun j hj => absurd hj (Nat.not_lt_zero _), Env.Chg.refl _ _, rfl, rfl, rfl⟩)
    fun t ⟨Bt, Ht, Ct, rdt, wrt, syt⟩ => ?_
  · -- One hash.
    obtain word : ∀ d, d + 4 ≤ sState → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
      fun d hd => Env.Chg.word v Ct (by simp only [sState] at hd; omega_arith) fun o ho => ⟨(Apx o ho).1, by
        simp only [pxRanges, List.mem_singleton] at ho; subst ho; right; exact hd⟩
    obtain hjc : j ≤ g.count := by omega_arith
    refine WP.mono (pHash_ok G v hq Bt hk (offset := offset) (j := j) (by rw [word fSeed (by simp only [fSeed, hdr, sState]; omega_arith), hS])
      (by rw [word fOffset (by simp only [fOffset, hdr, sState]; omega_arith), hO]) (by omega_arith) hjc)
      fun t' ⟨B', H', C', rd', wr', sy'⟩ => ⟨B', fun j' hj' => ?_, Ct.trans (C'.widen fun o ho => ?_),
        rd'.trans rdt, wr'.trans wrt, sy'.trans syt⟩
    · by_cases he : j' = j
      · subst he; exact H'
      obtain hm : (j' + 1) * g.qLen ≤ j * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
      obtain hs : (j + 1) * g.qLen = j * g.qLen + g.qLen := Nat.succ_mul _ _
      obtain hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
      rw [Env.Chg.scratch v C' (by simp only [hashAt, sX]; omega_arith) fun o ho => ?_, Ht j' (by omega_arith)]
      refine ⟨(hRanges_apart G v hjc o ho).1, ?_⟩
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX] <;> omega_arith
    · have hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
      obtain hs : (j + 1) * g.qLen = j * g.qLen + g.qLen := Nat.succ_mul _ _
      refine ⟨(sState, sX + g.pLen - sState), by simp [pxRanges], ?_⟩
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX] <;> omega_arith
  · -- The shaping.
    simp only [seqs]
    rw [show orByte (sX + g.pLen - 1) 1 = orByte (sX + g.pLen - 1) 1 ++ [] from (List.append_nil _).symm]
    refine orByte_ok Bt.scr (by simp only [sX]; omega_arith) (by decide) fun t₁ g₁ rd₁ wr₁ sy₁ m₁ =>
      orByte_ok (Scr.of_eq Bt.scr (g₁ _ (by decide)) (g₁ _ (by decide)) wr₁) (by simp only [sX]; omega_arith)
        (by decide) fun t₂ g₂ rd₂ wr₂ sy₂ m₂ => WP.block_nil ?_
    rw [m₁] at m₂
    obtain aEq : off E.base (sX + g.pLen - 1) = off E.base sX + BitVec.ofNat 64 (g.pLen - 1) := by
      rw [off_add_ofNat]; congr 1; omega_arith
    rw [aEq, shape_mem t.mem _ (by omega_arith) (by omega_arith)] at m₂
    obtain bl := VG.Proof.Bignum.bytesAt_length t.mem (off E.base sX) g.pLen
    obtain shaped : Spec.Rsa.bytesAt t₂.mem (off E.base sX) g.pLen =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Rsa.bytesAt t.mem (off E.base sX) g.pLen) 7 := by
      rw [m₂]
      conv => lhs; rw [← bl]
      refine VG.Proof.Dsa.Generation.qShape_memory (by omega_arith) (by omega_arith) fun i hi => ?_
      rw [bl] at hi
      simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some]
    -- The value of the hashes.
    obtain cl := chunk_length v B hk
    obtain digits := digits_value t.mem E.base (sX + g.pLen) g.qLen (pDigest (8 * g.qLen) (chunk E k) offset)
      g.count hcq fun j hj => by
        rw [show sX + g.pLen - (j + 1) * g.qLen = hashAt g j from rfl, Ht j (by omega_arith), pDig, pDigest, cl, hq]
    obtain suffix := bytesAt_suffix_value t.mem (off E.base (sX + g.pLen - (g.count + 1) * g.qLen))
      ((g.count + 1) * g.qLen - g.pLen) g.pLen
    obtain ho : VG.Proof.Bignum.off (off E.base (sX + g.pLen - (g.count + 1) * g.qLen))
        ((g.count + 1) * g.qLen - g.pLen) = off E.base sX := by
      rw [show VG.Proof.Bignum.off (off E.base (sX + g.pLen - (g.count + 1) * g.qLen))
        ((g.count + 1) * g.qLen - g.pLen) = off E.base (sX + g.pLen - (g.count + 1) * g.qLen +
          ((g.count + 1) * g.qLen - g.pLen)) from off_add_ofNat _ _ _]
      congr 1; omega_arith
    rw [ho, show (g.count + 1) * g.qLen - g.pLen + g.pLen = (g.count + 1) * g.qLen by omega_arith, digits,
      show (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) by rw [Nat.pow_mul]] at suffix
    obtain hne : Spec.Rsa.bytesAt t.mem (off E.base sX) g.pLen ≠ [] := by
      intro h; rw [h] at bl; simp only [List.length_nil] at bl; omega_arith
    obtain xv : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₂.mem (off E.base sX) g.pLen) =
        Spec.Ffdh.candidateOf (8 * g.pLen)
          (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) := by
      rw [shaped, decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value hne (by decide)
        (show 8 * g.pLen = _ by rw [bl]; omega_arith), ← decodeBE_os2ip, ← suffix,
        candidateOf_mod_width (by omega_arith) (Nat.le_refl _)]
    -- What changed.
    obtain px : (sState, sX + g.pLen - sState) ∈ pxRanges g := by simp [pxRanges]
    obtain C₂ : E.Chg (pxRanges g) s.mem t₂.mem := by
      rw [m₂]
      obtain h1 := Ct.byte px (i := sX - sState) (by simp only [sX, sState]; omega_arith)
        (by simp only [sX, sState]; omega_arith)
        (t.mem (off E.base sX) ||| 128#8)
      rw [off_add_ofNat, show sState + (sX - sState) = sX by simp only [sX, sState]] at h1
      obtain h2 := h1.byte px (i := sX - sState + (g.pLen - 1))
        (by simp only [sX, sState]; omega_arith) (by simp only [sX, sState]; omega_arith)
        (t.mem (off E.base sX + BitVec.ofNat 64 (g.pLen - 1)) ||| 1#8)
      rwa [off_add_ofNat, show sState + (sX - sState + (g.pLen - 1)) = sX + (g.pLen - 1) by
        simp only [sX, sState]; omega_arith, ← off_add_ofNat E.base sX] at h2
    obtain edi₂ : t₂.gpr .edi = s.gpr .edi := by rw [g₂ _ (by decide), g₁ _ (by decide)]; exact BitVec.eq_of_toNat_eq (by rw [Bt.scr.edi_toNat, B.scr.edi_toNat])
    exact ⟨B.keep v C₂ Apx edi₂ (by rw [g₂ _ (by decide), g₁ _ (by decide), Bt.sp, B.sp])
      (by rw [rd₂, rd₁, rdt]) (by rw [wr₂, wr₁, wrt]) (by rw [sy₂, sy₁, syt]), xv, C₂,
      by rw [rd₂, rd₁, rdt], by rw [wr₂, wr₁, wrt], by rw [sy₂, sy₁, syt]⟩

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.Arith`, which only this module used -/

section

/-! # p from `X` and q (A.1.1.2 steps 11.4–11.5)

`c = X mod 2 q` and `p = X − c + 1`, with `p − 1` and `(p − 1) / q` for the
generator, by RSA's fixed-count division. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- The bytes of a range apart from a change. -/
theorem outside_bytesAt {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d len : Nat}
    (hd : d + len ≤ o ∨ o + n ≤ d) (hd' : d + len < 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off base d) len = Spec.Rsa.bytesAt m (off base d) len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact h _ (by rw [ofs_off base (by omega_using [hd', hi])]; omega_using [hd, hi])

/-- A frame of one range of `scratch` changes nothing outside it. -/
theorem outside_of_frame {base : Addr} {d len : Nat} {m m' : Mem} (F : Frame [⟨off base d, len⟩] m m')
    (fit : d + len ≤ 2 ^ 64) : Outside base d len m m' := by
  intro x hx
  refine F x fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  obtain I := Offset.lt_iff x base fit
  change ¬ ((x - off base d).toNat + 1 ≤ len)
  change (x - off base d).toNat < len ↔ d ≤ ofs base x ∧ ofs base x < d + len at I
  omega_using [hx, I]

theorem add_no_carry {a b k : Nat} {c : Bool} (h : a + 2 ^ k * c.toNat = b) (hb : b < 2 ^ k) : a = b := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h <;> omega_arith

theorem sub_no_borrow {a r x k : Nat} {c : Bool} (h : a + r = x + 2 ^ k * c.toNat) (ha : a < 2 ^ k)
    (hr : r ≤ x) : a = x - r := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h <;> omega_arith

/-- `k + 1` words whose value fits in `k` are that value in `k`. -/
theorem val32_low {m : Mem} {base : Addr} {d k v : Nat} (h : val32 m base d (k + 1) = v) (hv : v < 2 ^ (32 * k)) :
    val32 m base d k = v := by
  rw [val32_append] at h
  have := val32_lt m base d k
  obtain hm : 2 ^ (32 * k) * val32 m base (d + 4 * k) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * k) 1) with h0 | h0
    · rw [h0, Nat.mul_zero]
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) h0; omega_using [h, hv, this]
  omega_using [h, hm]

/-- The division's arrays. -/
def divGeo (base : Addr) (size n : Nat) : VG.Proof.Rsa.X86.Div.Geometry :=
  { base := base, size := size, n := n, offsets := fun i => arr i.val }

/-- The arrays the arithmetic writes, and p in p||q||g. -/
def aRanges (pLen : Nat) : List (Nat × Nat) := [(arr 0, 4400), (sPk, pLen)]

/-- p's arithmetic: `p − 1 = X − X mod 2 q`, `(p − 1) / q` and `p`, in their
arrays and p in p||q||g. -/
theorem pArith_ok {pLen qLen : Nat} (hl : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) (hq : 20 ≤ qLen ∧ qLen ≤ 32)
    {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : 73728 ≤ size) {X Q : Nat}
    (hX : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base sX) pLen) = X)
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base (sPk + pLen)) qLen) = Q) (hQ0 : 0 < Q) :
    WP isa (pArith pLen qLen) s fun t =>
      val32 t.mem base aPm1 (pLen / 4) = X - X % (2 * Q) ∧
      val32 t.mem base aE (pLen / 4) = (X - X % (2 * Q)) / Q ∧
      val32 t.mem base aP (pLen / 4) = X - X % (2 * Q) + 1 ∧
      Spec.Rsa.bytesAt t.mem (off base sPk) pLen = Spec.Dsa.encodeBE pLen (X - X % (2 * Q) + 1) ∧
      Outs base (aRanges pLen) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      val32 t.mem base aOne (pLen / 4) = 1 := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  -- The sizes.
  obtain ⟨n, hn⟩ : ∃ n, n = pLen / 4 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = pLen / 8 := ⟨_, rfl⟩
  obtain h2 : 2 * h = n := by rcases hl with rfl | rfl | rfl <;> subst hn hh <;> rfl
  obtain h8 : 8 * h = pLen := by rcases hl with rfl | rfl | rfl <;> subst hh <;> rfl
  obtain n4 : 4 * n = pLen := by omega_arith
  obtain nle : n ≤ 96 := by omega_arith
  obtain npos : 0 < n := by omega_arith
  obtain Xlt : X < 2 ^ (32 * n) := by
    have := decodeBE_lt (Spec.Rsa.bytesAt s.mem (off base sX) pLen)
    rw [VG.Proof.Bignum.bytesAt_length, hX, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at this
    rwa [show 8 * pLen = 32 * n by omega_arith] at this
  obtain Qlt : Q < 2 ^ (32 * n) := by
    have := decodeBE_lt (Spec.Rsa.bytesAt s.mem (off base (sPk + pLen)) qLen)
    rw [VG.Proof.Bignum.bytesAt_length, hQ, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_arith))
  obtain Q2lt : 2 * Q < 2 ^ (32 * n) := by
    have := decodeBE_lt (Spec.Rsa.bytesAt s.mem (off base (sPk + pLen)) qLen)
    rw [VG.Proof.Bignum.bytesAt_length, hQ, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at this
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * qLen + 1 ≤ 32 * n by omega_arith)
    rw [Nat.pow_succ] at this
    omega_arith
  unfold pArith
  rw [← hn, ← hh]
  simp only [seqs]
  obtain sz : ∀ k, k ≤ 11 → arr k + 400 ≤ size := fun k hk => by simp only [arr]; omega_arith
  obtain R0 : ∀ {m m' : Mem} {o len : Nat}, Outside base o len m m' → arr 0 ≤ o → o + len ≤ arr 0 + 4400 →
      Outs base (aRanges pLen) m m' := fun O h₁ h₂ =>
    Outs.of_outside (O.mono h₁ h₂) (by simp [aRanges])
  -- X into the dividend and into its own array.
  refine WP.seq (WP.mono (loadS_ok hs (k := h) (o := aQt) (src := sX) (len := pLen) (by omega_arith)
    (by simp only [aQt, arr]; omega_arith) (by omega_arith) (by omega_arith) (by simp only [sX]; omega_arith)
    (by simp only [aQt, arr, sX]; omega_arith)) fun t₁ ⟨V₁, O₁, K₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.seq (WP.mono (loadS_ok hs₁ (k := h) (o := aX) (src := sX) (len := pLen) (by omega_arith)
    (by simp only [aX, arr]; omega_arith) (by omega_arith) (by omega_arith) (by simp only [sX]; omega_arith)
    (by simp only [aX, arr, sX]; omega_arith)) fun t₂ ⟨V₂, O₂, K₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  rw [outside_bytesAt O₁ (by simp only [aQt, arr, sX]; omega_arith) (by simp only [sX]; omega_arith), hX] at V₂
  rw [hX] at V₁
  -- q, with a zero word above it.
  refine WP.seq (WP.mono (loadS_ok hs₂ (k := h) (o := aTmp) (src := sPk + pLen) (len := qLen) (by omega_arith)
    (by simp only [aTmp, arr]; omega_arith) (by omega_arith) (by omega_arith) (by simp only [sPk]; omega_arith)
    (by simp only [aTmp, arr, sPk]; omega_arith)) fun t₃ ⟨V₃, O₃, K₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  rw [outside_bytesAt O₂ (by simp only [aX, arr, sPk]; omega_arith) (by simp only [sPk]; omega_arith),
    outside_bytesAt O₁ (by simp only [aQt, arr, sPk]; omega_arith) (by simp only [sPk]; omega_arith), hQ] at V₃
  refine WP.seq (wp_movi fun t₃' u₃ => st_ok (Scr.of_eq hs₃ (u₃.other _ (by decide)) (u₃.other _ (by decide))
    u₃.wr) (d := aTmp + 4 * n) (by simp only [aTmp, arr]; omega_arith) fun t₄ M₄ => WP.block_nil ?_)
  obtain m₄ : t₄.mem = t₃.mem.writeW (off base (aTmp + 4 * n)) (0 : BitVec 32) := by rw [M₄.mem, u₃.mem, u₃.gpr]
  obtain O₄ : Outside base (aTmp + 4 * n) 4 t₃.mem t₄.mem := m₄ ▸ writeW32_outside _ _ _ (by simp only [aTmp, arr]; omega_arith)
  obtain K₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₃ t₄ :=
    ⟨fun r hr => by rw [M₄.gpr, u₃.other r (fun e => hr (e ▸ List.mem_cons_self ..))], by rw [M₄.rd, u₃.rd],
      by rw [M₄.wr, u₃.wr]⟩
  obtain hs₄ := hs₃.of_keeps K₄ (by decide)
  obtain V₄ : val32 t₄.mem base aTmp (n + 1) = Q := by
    obtain V₃' : val32 t₃.mem base aTmp n = Q := by rw [← h2]; exact V₃
    rw [val32_append, O₄.val32 (by omega_arith) (by simp only [aTmp, arr]; omega_arith), V₃']
    simp only [val32, m₄, w32_write_self]
    show Q + 2 ^ (32 * n) * (0 + 2 ^ 32 * 0) = Q
    simp only [Nat.mul_zero, Nat.add_zero]
  -- The divisor `2 q`.
  refine WP.seq (WP.mono (chainAddW_ok hs₄ (k := n + 1) (o := aDv) (a := aTmp) (b := aTmp) (by omega_arith)
    (by simp only [aDv, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)
    (by simp only [aDv, aTmp, arr]; omega_arith) (by simp only [aDv, aTmp, arr]; omega_arith))
    fun t₅ ⟨O₅, ⟨c₅, _, E₅⟩, K₅⟩ => ?_)
  obtain hs₅ := hs₄.of_keeps K₅ (by decide)
  rw [V₄] at E₅
  obtain V₅ : val32 t₅.mem base aDv (n + 1) = 2 * Q :=
    add_no_carry (E₅.trans (by omega_arith)) (by rw [pow32_succ]; have := Nat.two_pow_pos (32 * n); omega_arith)
  -- The quotient and remainder.
  obtain X₅ : val32 t₅.mem base aQt n = X := by
    rw [O₅.val32 (by simp only [aDv, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith),
      O₄.val32 (by simp only [aTmp, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith),
      O₃.val32 (by simp only [aTmp, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith),
      O₂.val32 (by simp only [aX, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith), ← h2, V₁]
  obtain ctx : VG.Proof.Rsa.X86.Div.Context (divGeo base size n) t₅ := by
    refine ⟨hs₅, npos, by show n < 2 ^ 24; omega_arith, fun i => ?_, fun i j ne => ?_⟩
    · have := i.isLt
      show arr i.val + 4 * (if i = 0 then n else n + 1) ≤ size
      have := sz i.val (by omega_arith)
      split <;> omega_arith
    · have hij : i.val ≠ j.val := fun e => ne (Fin.ext e)
      have := i.isLt; have := j.isLt
      show arr i.val + 4 * (if i = 0 then n else n + 1) ≤ arr j.val ∨
        arr j.val + 4 * (if j = 0 then n else n + 1) ≤ arr i.val
      simp only [arr]
      split <;> split <;> omega_arith
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.code_ok ctx) fun t₆ ⟨_, Os₆, K₆, R₆⟩ => ?_)
  obtain v0 : ∀ m, (divGeo base size n).value m 0 = val32 m base aQt n := fun _ => rfl
  obtain v1 : ∀ m, (divGeo base size n).value m 1 = val32 m base aRm (n + 1) := fun _ => rfl
  obtain v2 : ∀ m, (divGeo base size n).value m 2 = val32 m base aDv (n + 1) := fun _ => rfl
  rw [v2, V₅] at R₆
  obtain ⟨R₆, Q₆⟩ := R₆ (by omega_arith) Q2lt
  rw [v1, v0, X₅] at R₆
  rw [v0, v0, X₅] at Q₆
  obtain hs₆ := hs₅.of_keeps K₆ (by decide)
  obtain Ofar : ∀ {d k : Nat}, 4 ≤ d → d ≤ 10 → k ≤ n →
      val32 t₆.mem base (arr d) k = val32 t₅.mem base (arr d) k := fun h₁ h₂ hk =>
    Os₆.val32 (fun r hr => by
      simp only [VG.Proof.Rsa.X86.Div.Geometry.ranges, divGeo, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [arr] <;> omega_arith) (by simp only [arr]; omega_arith)
  -- `p − 1 = X − X mod 2 q`.
  obtain M₆ : X % (2 * Q) < 2 ^ (32 * n) := Nat.lt_of_le_of_lt (Nat.mod_le _ _) Xlt
  obtain Rm₆ : val32 t₆.mem base aRm n = X % (2 * Q) := val32_low R₆ M₆
  obtain X₆ : val32 t₆.mem base aX n = X := by
    rw [show aX = arr 4 from rfl, Ofar (by decide) (by decide) (Nat.le_refl _),
      O₅.val32 (by simp only [aDv, arr]; omega_arith) (by simp only [arr]; omega_arith),
      O₄.val32 (by simp only [aTmp, arr]; omega_arith) (by simp only [arr]; omega_arith),
      O₃.val32 (by simp only [aTmp, arr]; omega_arith) (by simp only [arr]; omega_arith), ← h2]
    exact V₂
  refine WP.seq (WP.mono (chainSubW_ok hs₆ (k := n) (o := aPm1) (a := aX) (b := aRm) npos
    (by simp only [aPm1, arr]; omega_arith) (by simp only [aX, arr]; omega_arith) (by simp only [aRm, arr]; omega_arith)
    (by simp only [aPm1, aX, arr]; omega_arith) (by simp only [aPm1, aRm, arr]; omega_arith))
    fun t₇ ⟨O₇, ⟨c₇, _, E₇⟩, K₇⟩ => ?_)
  obtain hs₇ := hs₆.of_keeps K₇ (by decide)
  rw [Rm₆, X₆] at E₇
  obtain P₇ : val32 t₇.mem base aPm1 n = X - X % (2 * Q) :=
    sub_no_borrow E₇ (val32_lt _ _ _ _) (Nat.mod_le _ _)
  -- `(p − 1) / q = 2 ⌊X / 2 q⌋`.
  obtain Qt₇ : val32 t₇.mem base aQt n = X / (2 * Q) := by
    rw [O₇.val32 (by simp only [aPm1, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith), Q₆]
  obtain dm := Nat.div_add_mod X (2 * Q)
  obtain dle : X / (2 * Q) ≤ Q * (X / (2 * Q)) := Nat.le_mul_of_pos_left _ hQ0
  obtain dQ : 2 * Q * (X / (2 * Q)) = 2 * (Q * (X / (2 * Q))) := Nat.mul_assoc _ _ _
  refine WP.seq (WP.mono (chainAddW_ok hs₇ (k := n) (o := aE) (a := aQt) (b := aQt) npos
    (by simp only [aE, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith)
    (by simp only [aE, aQt, arr]; omega_arith) (by simp only [aE, aQt, arr]; omega_arith))
    fun t₈ ⟨O₈, ⟨c₈, _, E₈⟩, K₈⟩ => ?_)
  obtain hs₈ := hs₇.of_keeps K₈ (by decide)
  rw [Qt₇] at E₈
  obtain E₈' : val32 t₈.mem base aE n = (X - X % (2 * Q)) / Q := by
    rw [add_no_carry E₈ (by omega_arith)]
    rw [show X - X % (2 * Q) = Q * (2 * (X / (2 * Q))) by
      rw [Nat.mul_left_comm, ← Nat.mul_assoc]; omega_arith, Nat.mul_div_cancel_left _ hQ0]
    omega_arith
  obtain P₈ : val32 t₈.mem base aPm1 n = X - X % (2 * Q) := by
    rw [O₈.val32 (by simp only [aE, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), P₇]
  -- 1, and `p`.
  refine WP.seq (WP.mono (setConstW_ok hs₈ (k := n) (o := aOne) (x := 1) npos
    (by simp only [aOne, arr]; omega_arith) (Nat.one_lt_two_pow (by omega_arith)))
    fun t₉ ⟨V₉, K₉, O₉⟩ => ?_)
  obtain hs₉ := hs₈.of_keeps K₉ (by decide)
  obtain P₉ : val32 t₉.mem base aPm1 n = X - X % (2 * Q) := by
    rw [O₉.val32 (by simp only [aOne, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), P₈]
  obtain E₉ : val32 t₉.mem base aE n = (X - X % (2 * Q)) / Q := by
    rw [O₉.val32 (by simp only [aOne, aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), E₈']
  refine WP.seq (WP.mono (chainAddW_ok hs₉ (k := n) (o := aP) (a := aPm1) (b := aOne) npos
    (by simp only [aP, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith)
    (by simp only [aP, aPm1, arr]; omega_arith) (by simp only [aP, aOne, arr]; omega_arith))
    fun t₁₀ ⟨O₁₀, ⟨c₁₀, _, E₁₀⟩, K₁₀⟩ => ?_)
  obtain hs₁₀ := hs₉.of_keeps K₁₀ (by decide)
  rw [P₉, V₉] at E₁₀
  obtain half : 2 ^ (32 * n) = 2 * 2 ^ (32 * n - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 32 * n = k + 1 := ⟨32 * n - 1, by omega_arith⟩
    rw [hk, Nat.pow_succ, Nat.mul_comm, Nat.add_sub_cancel]
  obtain P₁₀ : val32 t₁₀.mem base aP n = X - X % (2 * Q) + 1 := add_no_carry E₁₀ (by omega_arith)
  obtain Pm₁₀ : val32 t₁₀.mem base aPm1 n = X - X % (2 * Q) := by
    rw [O₁₀.val32 (by simp only [aP, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), P₉]
  obtain E₁₀' : val32 t₁₀.mem base aE n = (X - X % (2 * Q)) / Q := by
    rw [O₁₀.val32 (by simp only [aP, aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), E₉]
  -- p into p||q||g.
  refine WP.mono (storeS_ok hs₁₀ (o := aP) (dst := sPk) (len := pLen) (n := h) (by omega_arith) (by omega_arith)
    (by simp only [aP, arr]; omega_arith) (by simp only [sPk]; omega_arith) (by simp only [aP, sPk, arr]; omega_arith)
    (by rw [h2, P₁₀, show 8 * pLen = 32 * n by omega_arith]; omega_arith)) fun t ⟨B₁₁, F₁₁, K₁₁⟩ => ?_
  obtain O₁₁ := outside_of_frame F₁₁ (by simp only [sPk]; omega_arith)
  rw [h2, P₁₀] at B₁₁
  refine ⟨?_, ?_, ?_, B₁₁, ?_, ?_, ?_⟩
  · rw [O₁₁.val32 (by simp only [aPm1, sPk, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), Pm₁₀]
  · rw [O₁₁.val32 (by simp only [aE, sPk, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), E₁₀']
  · rw [O₁₁.val32 (by simp only [aP, sPk, arr]; omega_arith) (by simp only [aP, arr]; omega_arith), P₁₀]
  · have Os₆' : Outs base (aRanges pLen) t₅.mem t₆.mem := fun x hx => Os₆ x fun r hr => by
      have := hx (arr 0, 4400) (by simp [aRanges])
      simp only [VG.Proof.Rsa.X86.Div.Geometry.ranges, divGeo, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      simp only [arr] at this
      rcases hr with rfl | rfl | rfl <;> simp only [arr, divGeo, Fin.val_zero, Fin.val_one] <;> omega_arith
    refine (R0 O₁ (by simp only [aQt]; omega_arith) (by simp only [aQt, arr]; omega_arith)).trans
      ((R0 O₂ (by simp only [aX, arr]; omega_arith) (by simp only [aX, arr]; omega_arith)).trans
      ((R0 O₃ (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)).trans
      ((R0 O₄ (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)).trans
      ((R0 O₅ (by simp only [aDv, arr]; omega_arith) (by simp only [aDv, arr]; omega_arith)).trans
      (Os₆'.trans
      ((R0 O₇ (by simp only [aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith)).trans
      ((R0 O₈ (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith)).trans
      ((R0 O₉ (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith)).trans
      ((R0 O₁₀ (by simp only [aP, arr]; omega_arith) (by simp only [aP, arr]; omega_arith)).trans
      (Outs.of_outside O₁₁ (by simp [aRanges])))))))))))
  · exact K₁.trans (K₂.trans (K₃.trans (K₄.trans ((K₅.mono (by decide)).trans ((K₆.mono (by decide)).trans
      ((K₇.mono (by decide)).trans ((K₈.mono (by decide)).trans ((K₉.mono (by decide)).trans
      ((K₁₀.mono (by decide)).trans (K₁₁.mono (by decide)))))))))))
  · rw [O₁₁.val32 (by simp only [aOne, sPk, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith),
      O₁₀.val32 (by simp only [aP, aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), V₉]

end VG.Proof.Dsa.X86.Generation

end

end


/-! # One counter of p's search (A.1.1.2 steps 11.1–11.8)

The candidate of the counter's offset, its bit-length guard, and its
probable-prime test. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- The candidate at `offset` for seed `k` and q `Q`. -/
def pcand (g : Geo) (E : Env) (k offset Q : Nat) : Nat :=
  Spec.Dsa.pCandidate (8 * g.pLen) (8 * g.qLen) Q (chunk E k) offset

/-- `fP` after a tested candidate: 0 if the witnesses ran out, 1 for a
probable prime, and 4, still searching, for a composite. -/
def pCode : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 4

/-- The ranges a counter changes. -/
def paRanges (g : Geo) : List (Nat × Nat) :=
  pxRanges g ++ aRanges g.pLen ++ [(sPP, 8 * ppWords), (fRes, 4), (fUsed, 4), (fUsedOut, 8), (fP, 4)]

theorem paRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (paRanges g) := by
  have sz := v.size_ge
  have b := G.bounds
  intro o ho
  simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fOut, fWitLen, hdr] <;> omega_arith

/-- After a counter. -/
structure PAPost (E : Env) (g : Geo) (k offset Q used : Nat) (s t : State) : Prop where
  base : Base E t
  pk : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen (pcand g E k offset Q)
  pm1 : val32 t.mem E.base aPm1 (g.pLen / 4) = pcand g E k offset Q - 1
  e : val32 t.mem E.base aE (g.pLen / 4) = (pcand g E k offset Q - 1) / Q
  pv : val32 t.mem E.base aP (g.pLen / 4) = pcand g E k offset Q
  one : val32 t.mem E.base aOne (g.pLen / 4) = 1
  fp : t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32
    (if pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) then 4
      else pCode (Spec.Dsa.probablePrime (pcand g E k offset Q) (E.witT.drop used)))
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32
    (if pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) then used
      else nextUsed E.witLen used (Spec.Dsa.probablePrime (pcand g E k offset Q) (E.witT.drop used)))
  chg : E.Chg (paRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The top bit of a byte, as `and eax, 0x80; cmp eax, 0` tests it. -/
theorem and80 (b : Byte) :
    ((b.setWidth 32 &&& (0x80 : BitVec 32)) - 0 == 0) = decide (b.toNat < 128) := by
  have hb := b.isLt
  obtain key : ∀ x < 256, (x &&& 128 = 0 ↔ x < 128) := by decide +kernel
  obtain e : ((b.setWidth 32 &&& (0x80 : BitVec 32)) - 0).toNat = b.toNat &&& 128 := by
    rw [BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_setWidth]
    show (2 ^ 32 - 0 + (b.toNat % 2 ^ 32 &&& 128)) % 2 ^ 32 = b.toNat &&& 128
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_using [])]
    have : b.toNat &&& 128 < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left (by omega_using [])
    omega_using [this]
  by_cases h : b.toNat < 128
  · simp only [h, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e, (key _ hb).mpr h]; rfl)
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [e] at this
    exact h ((key _ hb).mp this)

theorem status_lt (r : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status r < 2 ^ 32 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp [Proof.Dsa.ProbablePrime.status]

theorem pCode_zero {r : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status r = 0) :
    pCode r = 0 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status, pCode]

theorem pCode_one {r : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status r = 1) :
    pCode r = 1 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status, pCode]

theorem pCode_other {r : Option (Bool × Spec.RsaKeyGen.Rand)} (h₀ : Proof.Dsa.ProbablePrime.status r ≠ 0)
    (h₁ : Proof.Dsa.ProbablePrime.status r ≠ 1) : pCode r = 4 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status, pCode]

/-- After X, p and its guard: the guard's flag, p and its arrays, and the
state words the test reads. -/
structure PAFront (E : Env) (g : Geo) (k offset Q used : Nat) (s t : State) : Prop where
  base : Base E t
  zf : isa.eval .e t = some (decide (pcand g E k offset Q < 2 ^ (8 * g.pLen - 1)))
  pk : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen (pcand g E k offset Q)
  pm1 : val32 t.mem E.base aPm1 (g.pLen / 4) = pcand g E k offset Q - 1
  e : val32 t.mem E.base aE (g.pLen / 4) = (pcand g E k offset Q - 1) / Q
  pv : val32 t.mem E.base aP (g.pLen / 4) = pcand g E k offset Q
  one : val32 t.mem E.base aOne (g.pLen / 4) = 1
  fp : t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used
  chg : E.Chg (paRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms
  odd : pcand g E k offset Q % 2 = 1
  lt : pcand g E k offset Q < 2 ^ (8 * g.pLen)

/-- p from X, and the guard `p ≥ 2^(L − 1)`. -/
theorem paMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₁ : State} {k offset : Nat}
    (X₁ : XPost E g k offset s t₁) {Q : Nat}
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q) (hQ0 : 0 < Q)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used)
    (hP4 : s.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4) :
    WP isa (.seq (pArith g.pLen g.qLen)
      (.block [.movzx8 .eax (sc sPk), .alu .and .eax (.imm 0x80), .alu .cmp .eax (.imm 0)])) t₁
      (PAFront E g k offset Q used s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  obtain Apa := paRanges_apart G v
  obtain hQ₁ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₁.mem (off E.base (sPk + g.pLen)) g.qLen) = Q := by
    rw [Env.Chg.scratch v X₁.chg (by simp only [sPk]; omega_using [sz, bd]) fun o ho => by
      simp only [pxRanges, List.mem_singleton] at ho; subst ho
      exact ⟨by simp only [sState, sX]; omega_using [sz, bd], by left; simp only [sState, sX, sPk]; omega_using []⟩, hQ]
  -- p.
  obtain lens : g.pLen = 128 ∨ g.pLen = 256 ∨ g.pLen = 384 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega_using [h]
  refine WP.seq (VG.X86.WP.mono_syms (pArith_ok lens ⟨bd.1, bd.2.1⟩ X₁.base.scr sz X₁.x hQ₁ hQ0)
    fun t₂ ⟨P₂, E₂, V₂, K₂, O₂, Kr₂, One₂⟩ sy₂ => ?_)
  obtain hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * g.qLen) bs).length = 8 * g.qLen := fun bs => by
    rw [← G.seedHash, G.hash.hash_length, G.N]
  obtain pEq : Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) -
      Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) % (2 * Q) + 1 =
      pcand g E k offset Q := by
    unfold pcand
    rw [pCandidate_shaped (by omega_using [bd]) hlen]
    have := Nat.mod_le (Spec.Ffdh.candidateOf (8 * g.pLen)
      (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1))) (2 * Q)
    show _ = Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) + 1 -
      Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) % (2 * Q)
    omega_using [this]
  obtain Xsh := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * g.pLen) (by omega_using [bd])
    (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1))
  generalize Spec.Ffdh.candidateOf (8 * g.pLen)
    (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) = X
    at P₂ E₂ V₂ K₂ pEq Xsh
  generalize hpc : pcand g E k offset Q = pc at pEq
  obtain dm := Nat.div_add_mod X (2 * Q)
  obtain ml := Nat.mod_le X (2 * Q)
  obtain dQ : 2 * Q * (X / (2 * Q)) = 2 * (Q * (X / (2 * Q))) := Nat.mul_assoc _ _ _
  obtain pcOdd : pc % 2 = 1 := by omega_using [pEq, dm, dQ]
  obtain pcLt : pc < 2 ^ (8 * g.pLen) := by omega_using [Xsh, pEq, pcOdd]
  obtain e256 : (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) := by rw [Nat.pow_mul]
  rw [pEq] at V₂ K₂
  rw [show X - X % (2 * Q) = pc - 1 by omega_using [pEq]] at P₂ E₂
  -- What changed so far.
  obtain Aa : E.Apart (aRanges g.pLen) := fun o ho => Apa o
    (List.mem_append_left _ (List.mem_append_right _ ho))
  have Ca : E.Chg (aRanges g.pLen) t₁.mem t₂.mem := Env.Chg.of_frame
    (VG.Proof.Bignum.outs_frame O₂ fun r hr => by
      simp only [aRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [arr, sPk] <;> omega_arith) fun r hr => by
    simp only [List.mem_map] at hr
    obtain ⟨o, ho, rfl⟩ := hr
    exact Env.in_range ho (Nat.le_refl _) (Nat.le_refl _)
  obtain B₂ : Base E t₂ := X₁.base.keep v Ca Aa (Kr₂.1 _ (by decide)) (Kr₂.1 _ (by decide)) Kr₂.2.1 Kr₂.2.2 sy₂
  obtain C₂' : E.Chg (pxRanges g ++ aRanges g.pLen) s.mem t₂.mem :=
    (X₁.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩).trans
      (Ca.widen fun o ho => ⟨o, List.mem_append_right _ ho, Nat.le_refl _, Nat.le_refl _⟩)
  obtain inPa : ∀ o ∈ pxRanges g ++ aRanges g.pLen, ∃ o' ∈ paRanges g, o'.1 ≤ o.1 ∧ o.1 + o.2 ≤ o'.1 + o'.2 :=
    fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩
  obtain C₂ : E.Chg (paRanges g) s.mem t₂.mem := C₂'.widen inPa
  obtain word₂ : ∀ d, d + 4 ≤ sState → t₂.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    fun d hd => Env.Chg.word v C₂' (by simp only [sState] at hd; omega_using [sz, hd]) fun o ho => by
      simp only [pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [sState, sX, arr, sPk] at hd ⊢ <;> omega_arith
  obtain hP₂ : t₂.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
    rw [word₂ fP (by simp only [fP, hdr, sState]; omega_using []), hP4]
  obtain hU₂ : t₂.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [word₂ fUsed (by simp only [fUsed, hdr, sState]; omega_using []), hU]
  -- The guard `p ≥ 2^(L − 1)`, by p's first byte.
  obtain hb : t₂.mem (off E.base sPk) = (Spec.Dsa.encodeBE g.pLen pc).getD 0 0 := by
    have := congrArg (fun l : List Byte => l.getD 0 0) K₂
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show 0 < g.pLen by omega_using [bd]), Option.map_some, Option.getD_some] at this
    rw [List.getD_eq_getElem?_getD, ← this, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  obtain top : (t₂.mem (off E.base sPk)).toNat < 128 ↔ pc < 2 ^ (8 * g.pLen - 1) := by
    rw [hb]; exact candidate_firstByte (by omega_using [bd]) (by rw [e256]; exact pcLt)
  refine ld8_ok B₂.scr (d := sPk) (by simp only [sPk]; omega_using [sz]) fun s₃ u₃ => wp_andi fun s₄ u₄ =>
    wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ?_
  obtain zf₅ : isa.eval .e s₅ = some (decide ((t₂.mem (off E.base sPk)).toNat < 128)) := by
    show s₅.zf = _
    rw [z₅, u₄.gpr, u₃.gpr, and80]
  obtain m₅ : s₅.mem = t₂.mem := by rw [f₅.mem, u₄.mem, u₃.mem]
  obtain regs₅ : ∀ r, r ≠ .eax → s₅.gpr r = t₂.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr, u₃.other r hr]
  obtain rd₅ : s₅.rd = t₂.rd := by rw [f₅.rd, u₄.rd, u₃.rd]
  obtain wr₅ : s₅.wr = t₂.wr := by rw [f₅.wr, u₄.wr, u₃.wr]
  obtain sy₅ : s₅.syms = t₂.syms := by rw [f₅.syms, u₄.syms, u₃.syms]
  obtain B₅ : Base E s₅ := B₂.regs m₅ (regs₅ _ (by decide)) (regs₅ _ (by decide)) rd₅ wr₅ sy₅
  obtain rd₂ : t₂.rd = s.rd := by rw [Kr₂.2.1, X₁.rd]
  obtain wr₂ : t₂.wr = s.wr := by rw [Kr₂.2.2, X₁.wr]
  obtain sy₂s : t₂.syms = s.syms := by rw [sy₂, X₁.syms]
  subst hpc
  refine ⟨B₅, by rw [zf₅]; exact congrArg some (decide_eq_decide.mpr top), by rw [m₅]; exact K₂,
    by rw [m₅]; exact P₂, by rw [m₅]; exact E₂, by rw [m₅]; exact V₂, by rw [m₅]; exact One₂,
    by rw [m₅]; exact hP₂, by rw [m₅]; exact hU₂, by rw [m₅]; exact C₂, by rw [rd₅, rd₂], by rw [wr₅, wr₂],
    by rw [sy₅, sy₂s], pcOdd, pcLt⟩

theorem pAttempt_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid)
    (hq : E.qLen = g.qLen) {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {offset : Nat} (hO : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset)
    (hoff : offset + g.count + 256 ≤ 2 ^ 32) {Q : Nat}
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q) (hQ0 : 0 < Q)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen)
    (hP4 : s.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4) :
    WP isa g.pAttempt s (PAPost E g k offset Q used s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  obtain Apa := paRanges_apart G v
  unfold Geo.pAttempt
  simp only [seqs]
  refine WP.seq (WP.mono (pX_ok G v hq B hk hS hO hoff) fun t₁ X₁ =>
    WP.assoc (WP.seq (WP.mono (paMid_ok G v X₁ hQ hQ0 hU hP4) fun s₅ F => ?_)))
  have B₅ := F.base
  refine WP.ite (decide (pcand g E k offset Q < 2 ^ (8 * g.pLen - 1))) F.zf (fun hlo => WP.block_nil ?_) (fun hhi => ?_)
  · -- Below `2^(L − 1)`: skipped.
    obtain hlt : pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) := of_decide_eq_true hlo
    refine ⟨B₅, F.pk, F.pm1, F.e, F.pv, F.one, ?_, ?_, F.chg, F.rd, F.wr, F.syms⟩
    · simp only [F.fp, hlt, ↓reduceIte]
    · simp only [F.used, hlt, ↓reduceIte]
  -- At least `2^(L − 1)`: tested.
  obtain hge : ¬ pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) := of_decide_eq_false hhi
  have pcOdd := F.odd
  have pcLt := F.lt
  obtain e256 : (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) := by rw [Nat.pow_mul]
  obtain lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  obtain candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate + g.pLen ≤ 8 * ppWords := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega_arith
  obtain szT : VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width (8 * g.pLen)) ≤
      8 * ppWords := by simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at candLe; omega_arith
  refine WP.seq (VG.X86.WP.mono_syms (copyS_ok B₅.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate) (src := sPk) (n := g.pLen)
    (by omega_arith) (by simp only [sPP, ppWords] at candLe ⊢; omega_arith) (by simp only [sPk]; omega_arith)
    (by right; simp only [sPP, sPk]; omega_arith)) fun t₆ ⟨R₆, F₆, K₆⟩ sy₆ => ?_)
  obtain pp : (sPP, 8 * ppWords) ∈ paRanges g := by simp [paRanges]
  obtain C₆ : E.Chg [(sPP, 8 * ppWords)] s₅.mem t₆.mem := Env.Chg.of_frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (List.mem_singleton_self _) (by omega_arith) (by omega_arith)
  obtain App : E.Apart [(sPP, 8 * ppWords)] := fun o ho => Apa o (by simp only [List.mem_singleton] at ho; rw [ho]; exact pp)
  obtain B₆ : Base E t₆ := B₅.keep v C₆ App (K₆.1 _ (by decide)) (K₆.1 _ (by decide)) K₆.2.1 K₆.2.2 sy₆
  obtain hU₆ : t₆.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v C₆ (by simp only [fUsed, hdr]; omega_arith) (fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sPP, ppWords, fUsed, hdr]; omega_arith), F.used]
  obtain hP₆ : t₆.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
    rw [Env.Chg.word v C₆ (by simp only [fP, hdr]; omega_arith) (fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sPP, ppWords, fP, hdr]; omega_arith), F.fp]
  obtain cval : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)) t₆.mem
      (off E.base sPP) = pcand g E k offset Q := by
    unfold Proof.Dsa.ProbablePrime.candidateAt
    obtain b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).bits / 8 = g.pLen := by
      show 8 * g.pLen / 8 = g.pLen; omega_arith
    rw [b8, VG.Offset.add_add, R₆, F.pk, decodeBE_encodeBE (by rw [e256]; exact pcLt)]
  obtain plen : Spec.Dsa.bitLength (pcand g E k offset Q) = 8 * g.pLen :=
    (bitLength_iff_bounds (by omega_arith)).mpr ⟨by omega_arith, pcLt⟩
  refine WP.seq (VG.X86.WP.mono_syms (test_ok G.pv G.pNoSp G.pStack v B₆ hU₆ hu lay (by rw [cval]; exact pcOdd)
    (by rw [cval]; exact plen)) fun t₇ P sy₇ => ?_)
  rw [cval] at P
  obtain ⟨r, hr⟩ : ∃ r, Spec.Dsa.probablePrime (pcand g E k offset Q) (E.witT.drop used) = r := ⟨_, rfl⟩
  have res₇ := P.res
  have used₇ := P.used
  rw [hr] at res₇ used₇
  -- The ranges the test changed are the counter's.
  obtain Cp : E.Chg (paRanges g) s.mem t₇.mem := by
    refine (F.chg.trans (C₆.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact pp,
      Nat.le_refl _, Nat.le_refl _⟩)).trans (P.chg.widen fun o ho => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact ⟨_, pp, Nat.le_refl _, by omega_arith⟩
    · exact ⟨_, by simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩
  obtain testR : ∀ o ∈ [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width
      (8 * g.pLen))), (fRes, 4), (fUsed, 4), (fUsedOut, 8)], o.1 + o.2 ≤ E.size := fun o ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, ppWords, fRes, fUsed, fUsedOut, hdr] at szT ⊢ <;> omega_arith
  obtain keep7 : ∀ {d k : Nat}, d + 4 * k ≤ sPP → 7400 ≤ d →
      val32 t₇.mem E.base d k = val32 s₅.mem E.base d k := fun h₁ h₂ => by
    rw [Env.Chg.val32 v P.chg (by simp only [sPP] at h₁; omega_arith) fun o ho => ⟨testR o ho, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, fRes, fUsed, fUsedOut, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩,
      (outside_of_frame F₆ (by simp only [sPP, ppWords] at candLe ⊢; omega_arith)).val32
        (by left; simp only [sPP] at h₁ ⊢; omega_arith) (by simp only [sPP] at h₁; omega_arith)]
  obtain fin : ∀ t : State, Base E t → E.Chg [(fP, 4)] t₇.mem t.mem →
      t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 (pCode r) → t.rd = t₇.rd → t.wr = t₇.wr →
      t.syms = t₇.syms → PAPost E g k offset Q used s t := by
    intro t Bt Ct fpt rdt wrt syt
    obtain fPR : ∀ {d n : Nat}, d + n ≤ fP ∨ fP + 4 ≤ d → d + n ≤ E.size →
        ∀ o ∈ [(fP, 4)], o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + n ≤ o.1) := fun h₁ h₂ o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [fP, hdr] at h₁ ⊢; omega_arith
    obtain arrV : ∀ {d : Nat}, d + 4 * (g.pLen / 4) ≤ sPP → 7400 ≤ d →
        val32 t.mem E.base d (g.pLen / 4) = val32 s₅.mem E.base d (g.pLen / 4) := fun h₁ h₂ => by
      rw [Env.Chg.val32 v Ct (by simp only [sPP] at h₁; omega_arith) (fPR (by right; simp only [fP, hdr]; omega_arith)
        (by simp only [sPP] at h₁; omega_arith)), keep7 h₁ h₂]
    refine ⟨Bt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Cp.trans (Ct.widen fun o ho => ⟨o, by
        simp only [List.mem_singleton] at ho; rw [ho]; simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩),
      by rw [rdt, P.rd, K₆.2.1, F.rd], by rw [wrt, P.wr, K₆.2.2, F.wr],
      by rw [syt, P.syms, sy₆, F.syms]⟩
    · rw [Env.Chg.scratch v Ct (by simp only [sPk]; omega_arith) (fPR (by right; simp only [fP, sPk, hdr]; omega_arith)
        (by simp only [sPk]; omega_arith)),
        Env.Chg.scratch v P.chg (by simp only [sPk]; omega_arith) (fun o ho => ⟨testR o ho, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, sPk, fRes, fUsed, fUsedOut, hdr] <;> omega_arith⟩),
        frame_bytes F₆ (by right; simp only [sPP, sPk]; omega_arith) (by simp only [sPP, ppWords] at candLe ⊢; omega_arith)
          (by simp only [sPk]; omega_arith), F.pk]
    · rw [arrV (by simp only [aPm1, arr, sPP]; omega_arith) (by simp only [aPm1, arr]; omega_arith), F.pm1]
    · rw [arrV (by simp only [aE, arr, sPP]; omega_arith) (by simp only [aE, arr]; omega_arith), F.e]
    · rw [arrV (by simp only [aP, arr, sPP]; omega_arith) (by simp only [aP, arr]; omega_arith), F.pv]
    · rw [arrV (by simp only [aOne, arr, sPP]; omega_arith) (by simp only [aOne, arr]; omega_arith), F.one]
    · simp only [hge, ↓reduceIte, hr]; exact fpt
    · simp only [hge, ↓reduceIte, hr]
      rw [Env.Chg.word v Ct (by simp only [fUsed, hdr]; omega_arith) (fPR (by left; simp only [fUsed, fP, hdr]; omega_arith)
        (by simp only [fUsed, hdr]; omega_arith)), used₇]
  obtain Afp : E.Apart [(fP, 4)] := fun o ho => Apa o (by simp only [List.mem_singleton] at ho; rw [ho]; simp [paRanges])
  obtain store : ∀ (u u' : State) (c : Nat), Base E u → u.mem = t₇.mem →
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) → u'.mem = u.mem.writeW (off E.base fP) (BitVec.ofNat 32 c) →
      u'.rd = u.rd → u'.wr = u.wr → u'.syms = u.syms → u.rd = t₇.rd → u.wr = t₇.wr → u.syms = t₇.syms →
      c = pCode r → PAPost E g k offset Q used s u' := by
    intro u u' c Bu mu gu mu' rdu wru syu rdu₇ wru₇ syu₇ hc
    obtain Cu : E.Chg [(fP, 4)] t₇.mem u'.mem := by
      rw [mu', mu]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) _
    refine fin u' (Bu.keep v (by rw [mu]; exact Cu) Afp (gu _ (by decide)) (gu _ (by decide)) rdu wru syu) Cu
      (by rw [mu', Mem.readW_writeW_self32, hc]) (by rw [rdu, rdu₇]) (by rw [wru, wru₇]) (by rw [syu, syu₇])
  refine WP.seq (cmpF_end P.base.scr (o := fRes) (v := 0) (by simp only [fRes, hdr]; omega_arith) res₇ (status_lt r)
    (by decide) fun s₈ g₈ m₈ rd₈ wr₈ sy₈ z₈ => ?_)
  obtain B₈ : Base E s₈ := P.base.regs m₈ (g₈ _ (by decide)) (g₈ _ (by decide)) rd₈ wr₈ sy₈
  refine WP.ite _ z₈ (fun h0 => stImm_end B₈.scr (o := fP) (v := 0) (by simp only [fP, hdr]; omega_arith)
    fun s₉ g₉ m₉ rd₉ wr₉ sy₉ => store s₈ s₉ 0 B₈ m₈ g₉ m₉ rd₉ wr₉ sy₉ rd₈ wr₈ sy₈
      (pCode_zero (of_decide_eq_true h0)).symm) (fun h0 => ?_)
  refine WP.seq (cmpF_end B₈.scr (o := fRes) (v := 1) (by simp only [fRes, hdr]; omega_arith) (by rw [m₈]; exact res₇)
    (status_lt r) (by decide) fun s₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ sy₁₀ z₁₀ => ?_)
  obtain B₁₀ : Base E s₁₀ := B₈.regs m₁₀ (g₁₀ _ (by decide)) (g₁₀ _ (by decide)) rd₁₀ wr₁₀ sy₁₀
  refine WP.ite _ z₁₀ (fun h1 => stImm_end B₁₀.scr (o := fP) (v := 1) (by simp only [fP, hdr]; omega_arith)
    fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ => store s₁₀ s₁₁ 1 B₁₀ (by rw [m₁₀, m₈]) g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁
      (by rw [rd₁₀, rd₈]) (by rw [wr₁₀, wr₈]) (by rw [sy₁₀, sy₈]) (pCode_one (of_decide_eq_true h1)).symm)
    (fun h1 => WP.block_nil ?_)
  -- A composite: `fP` stays 4.
  obtain m : s₁₀.mem = t₇.mem := by rw [m₁₀, m₈]
  refine fin s₁₀ B₁₀ (by rw [m]; exact Env.Chg.refl _ _) ?_ (by rw [rd₁₀, rd₈]) (by rw [wr₁₀, wr₈])
    (by rw [sy₁₀, sy₈])
  rw [pCode_other (of_decide_eq_false h0) (of_decide_eq_false h1), m,
    Env.Chg.word v P.chg (by simp only [fP, hdr]; omega_arith) (fun o ho => ⟨testR o ho, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, fRes, fUsed, fUsedOut, fP, hdr] <;> omega_arith⟩), hP₆]

end VG.Proof.Dsa.X86.Generation
