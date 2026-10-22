module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Mont.X86.WordOps

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
  have e : VG.X86.addr (s.gpr .edx) 0 = off base d := by
    simp only [VG.X86.addr, he, BitVec.add_zero]; exact Scr.wide hs (by omega)
  refine cons (s' := s.setReg .eax ((s.mem (off base d)).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  have hin := hs.read (d := d) (n := 1) hd
  simp only [exec, State.load8, at_, ea_mk, e, hin, ↓reduceIte, Option.map_some]

/-- `mov byte [edx], al`, `edx` at `scratch + d`. -/
theorem stx_ok {d : Nat} (hs : Scr s base size) (hd : d + 1 ≤ size)
    (he : s.gpr .edx = s.gpr .edi + BitVec.ofNat 32 d)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) ((s.gpr .eax).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .edx 0) .al :: is)) s Q := by
  have e : VG.X86.addr (s.gpr .edx) 0 = off base d := by
    simp only [VG.X86.addr, he, BitVec.add_zero]; exact Scr.wide hs (by omega)
  refine cons (s' := { s with mem := s.mem.writeW (off base d) ((s.gpr .eax).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have hout := hs.write (d := d) (n := 1) hd
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

theorem encodeBE_length' (n x : Nat) : (Spec.Dsa.encodeBE n x).length = n := by
  simp [Spec.Dsa.encodeBE]

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
  have ht : Scr t base size := Scr.of_eq hs (hk.1 _ (by decide)) (hk.1 _ (by decide)) hk.2.2
  have hbt := hlow m (Nat.le_refl _)
  have hBm : (Spec.Rsa.bytesAt s.mem (off base o) n).take (m + 1) =
      (Spec.Rsa.bytesAt s.mem (off base o) n).take m ++ [s.mem (off base (o + m))] := by
    rw [List.take_add_one, getElem?_bytesAt _ _ (by omega), off_add_ofNat]; rfl
  have hBl := VG.Proof.Bignum.bytesAt_length s.mem (off base o) n
  generalize hB : Spec.Rsa.bytesAt s.mem (off base o) n = B at htake hhigh hBm hBl ⊢
  generalize hR : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE B + c) = R at htake hhigh ⊢
  have hRl : R.length = n := by rw [← hR, encodeBE_length']
  generalize s.mem (off base (o + m)) = b at hbt hBm
  have hbn := b.isLt
  have hsum : b.toNat + c' < 2 ^ 32 := by omega
  -- The step's result.
  have hR1 : R.take (m + 1) = Spec.Dsa.encodeBE m (Spec.Dsa.decodeBE (B.take m) + (b.toNat + c') / 256) ++
      [BitVec.ofNat 8 (b.toNat + c')] := by
    have h := seedAdd_snoc (B.take m) b c'
    rw [List.length_take, Nat.min_eq_left (by omega)] at h
    rw [htake, hBm, h]
  have hRm : R.take m = Spec.Dsa.encodeBE m (Spec.Dsa.decodeBE (B.take m) + (b.toNat + c') / 256) := by
    rw [show R.take m = (R.take (m + 1)).take m by rw [List.take_take, Nat.min_eq_left (by omega)], hR1,
      List.take_left' (encodeBE_length' _ _)]
  have hRg : R.getD m 0 = BitVec.ofNat 8 (b.toNat + c') := by
    rw [show R.getD m 0 = (R.take (m + 1)).getD m 0 by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, show m < m + 1 by omega, ↓reduceIte], hR1,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [encodeBE_length']), encodeBE_length',
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  -- The instructions.
  simp only [addStep]
  refine ldx_ok ht (d := o + m) (by omega) hedx fun s₁ u₁ => wp_add fun s₂ u₂ _ => ?_
  have di₂ : s₂.gpr .edi = t.gpr .edi := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have dx₂ : s₂.gpr .edx = t.gpr .edx := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have ax₂ : s₂.gpr .eax = BitVec.ofNat 32 (b.toNat + c') := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hc, hbt]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega), Nat.mod_eq_of_lt (a := c') (by omega)]
  have ht₂ : Scr s₂ base size := Scr.of_eq ht di₂ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.wr, u₁.wr])
  refine stx_ok ht₂ (d := o + m) (by omega) (by rw [dx₂, di₂, hedx]) fun s₃ M₃ =>
    wp_shr (n := 8) (by decide) fun s₄ u₄ _ => wp_mov fun s₅ u₅ => wp_subi fun s₆ u₆ _ _ =>
    wp_subi fun s₇ u₇ _ _ => wp_cmpi fun s₈ f₈ _ z₈ => WP.block_nil ?_
  have g₈ : ∀ r, r ∉ [.eax, .ecx, .edx, .esi] → s₈.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₈.gpr, u₇.other r hr.2.2.2, u₆.other r hr.2.2.1, u₅.other r hr.2.1, u₄.other r hr.1, M₃.gpr,
      u₂.other r hr.1, u₁.other r hr.1]
  have di₈ : s₈.gpr .edi = t.gpr .edi := g₈ _ (by decide)
  have m₈ : s₈.mem = t.mem.writeW (off base (o + m)) (BitVec.ofNat 8 (b.toNat + c')) := by
    rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, M₃.mem, ax₂, setWidth8_ofNat, u₂.mem, u₁.mem]
  have cx₈ : s₈.gpr .ecx = BitVec.ofNat 32 ((b.toNat + c') / 256) := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, M₃.gpr, ax₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (a := b.toNat + c') (by omega), Nat.mod_eq_of_lt (by omega)]
  have dx₈ : s₈.gpr .edx = t.gpr .edx - 1 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), M₃.gpr, dx₂]
  have si₈ : s₈.gpr .esi = BitVec.ofNat 32 m := by
    rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), M₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hesi]
    exact ofNat_pred (k := m + 1) (by omega)
  have zf₈ : s₈.zf = some (decide (m = 0)) := by
    rw [z₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), M₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hesi, ofNat_pred (k := m + 1) (by omega),
      Nat.add_sub_cancel]
    exact congrArg some (sub_beq (b := 0) (by omega) (by decide))
  have rd₈ : s₈.rd = s.rd := by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, M₃.rd, u₂.rd, u₁.rd, hk.2.1]
  have wr₈ : s₈.wr = s.wr := by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, M₃.wr, u₂.wr, u₁.wr, hk.2.2]
  have sy₈ : s₈.syms = s.syms := by
    rw [f₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, M₃.syms, u₂.syms, u₁.syms, hsy]
  have k₈ : Keeps [.eax, .ecx, .edx, .esi] s s₈ :=
    ⟨fun r hr => (g₈ r hr).trans (hk.1 r hr), rd₈, wr₈⟩
  have ne_m : ∀ i, i < n → i ≠ m → off base (o + i) ≠ off base (o + m) := fun i hi h =>
    Offset.add_ofNat_ne base (by omega) (by omega) (by omega)
  have fr₈ : Frame [⟨off base o, n⟩] s.mem s₈.mem := fun x hx => by
    have hin : (⟨off base o, n⟩ : Region).Contains (off base (o + m)) 1 := by
      rw [← off_add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
    have hne : x ≠ off base (o + m) := fun h => hx _ (List.mem_singleton_self _) (h ▸ hin)
    rw [m₈, WriteBytes.writeW8_apply, ite_eq_right_iff.mpr (fun h => absurd h hne), hfr x hx]
  refine ⟨zf₈, fun h0 => ⟨?_, fr₈, k₈, sy₈⟩, fun m' hm' => ⟨by omega, ?_, ?_, ?_, ?_, ?_, fr₈, k₈, sy₈⟩⟩
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
    · simp only [ne_m i hi hi0, ↓reduceIte, hhigh i (by omega) hi]
  · rw [si₈, hm']
  · rw [dx₈, di₈, hedx, hm', show o + (m' + 1) = (o + m') + 1 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · refine ⟨(b.toNat + c') / 256, cx₈, by omega, ?_⟩
    subst hm'
    rw [hB, hR, hRm]
  · intro i hi
    rw [m₈, WriteBytes.writeW8_apply]
    simp only [ne_m i (by omega) (by omega), ↓reduceIte, hlow i (by omega)]
  · intro i hi hin
    rw [m₈, WriteBytes.writeW8_apply, hB, hR]
    by_cases him : i = m
    · subst him; simp only [↓reduceIte, hRg]
    · simp only [ne_m i hin him, ↓reduceIte, hhigh i (by omega) hin]

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
    · exact .inr ⟨by simp [X86.eval, hz, h0], m - 1, by omega, hk (m - 1) (by omega)⟩
  · have hBl := VG.Proof.Bignum.bytesAt_length s.mem (off base o) n
    refine ⟨by omega, ?_, ?_, ⟨c, ?_, hc, ?_⟩, fun i _ => by rw [u₀.mem], fun i hi hi' => by omega,
      fun x _ => by rw [u₀.mem], ⟨fun r hr => u₀.other r fun h => hr (by simp [h]), u₀.rd, u₀.wr⟩, u₀.syms⟩
    · rw [u₀.gpr, Nat.sub_add_cancel hn]
    · rw [u₀.other _ (by decide), u₀.other _ (by decide), hedx, Nat.add_sub_assoc hn]
    · rw [u₀.other _ (by decide), hecx]
    · rw [Nat.sub_add_cancel hn, List.take_of_length_le (by rw [encodeBE_length']),
        List.take_of_length_le (by omega)]

end VG.Proof.Dsa.X86.Generation
