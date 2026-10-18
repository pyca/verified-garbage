module

public import VerifiedGarbage.Proof.Rsa.X86_64.PreOut
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_precompute` on x86-64: the computation

`main`, from the header its entry leaves (`vg_rsa_check_key`'s, `MainPre`
with `d` as `n`, `dP` and `qInv` as `p` and `dQ` as `q`, and `pre` in `e`'s
slots),
for a valid modulus: the workspace (`setupK_ok`), `p q = n` into `sMask`
(`pqN_ok`), then `n`, `R² mod n`, `R_p mod p` and `R_q mod q` to the words
past the arrays (`DWords`), and those, masked, to `pre` (`preMain_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey VG.Impl.Rsa.X86_64.PrivPre
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- The words `xs` at `B + d`. -/
def DWords (m : Mem) (B : Addr) (d : Nat) (xs : List (BitVec 64)) : Prop :=
  ∀ i (hi : i < xs.length), Bignum.word m B (d + 8 * i) = xs[i]

theorem DWords.append {m : Mem} {B : Addr} {d : Nat} {xs ys : List (BitVec 64)} (h₁ : DWords m B d xs)
    (h₂ : DWords m B (d + 8 * xs.length) ys) : DWords m B d (xs ++ ys) := by
  intro i hi
  rw [List.getElem_append]
  split
  · exact h₁ i ‹_›
  · rename_i hlt
    rw [List.length_append] at hi
    have := h₂ (i - xs.length) (by omega)
    rw [← this, show d + 8 * xs.length + 8 * (i - xs.length) = d + 8 * i by omega]

theorem DWords.of_copy {m m' : Mem} {B : Addr} {d e W c x : Nat}
    (hc : ∀ i < c, Bignum.word m' B (d + 8 * i) = Bignum.word m B (e + 8 * i)) (hx : wv m B e W = x)
    (hcW : c ≤ W) : DWords m' B d (Spec.Rsa.toWords x c) := by
  intro i hi
  simp only [Spec.Rsa.toWords, List.length_map, List.length_range] at hi
  rw [hc i hi, word_eq_ofNat m B e W (by omega), hx]
  simp [Spec.Rsa.toWords]

theorem DWords.frame {m m' : Mem} {B : Addr} {d : Nat} {xs : List (BitVec 64)} (h : DWords m B d xs)
    {o n : Nat} (ho : Outside B o n m m') (hd : d + 8 * xs.length ≤ o ∨ o + n ≤ d)
    (hd' : d + 8 * xs.length ≤ 2 ^ 64) : DWords m' B d xs :=
  fun i hi => (ho.word (by omega) (by omega)).trans (h i hi)

theorem DWords.arrays {m m' : Mem} {B : Addr} {w d : Nat} {js : List Nat} {xs : List (BitVec 64)}
    (h : DWords m B d xs) (ha : Arrays B w js m m') (hjs : ∀ j ∈ js, j < 8) (hd : slot w 8 ≤ d)
    (hd' : d + 8 * xs.length ≤ 2 ^ 64) : DWords m' B d xs :=
  fun i hi => (ha.word_eq (fun j hj => .inr (by have := slot_le (w := w) (hjs j hj); omega)) (by omega)).trans
    (h i hi)

theorem DWords.congr_toWords {m : Mem} {B : Addr} {d x y c : Nat} (h : DWords m B d (Spec.Rsa.toWords x c))
    (hxy : x = y) : DWords m B d (Spec.Rsa.toWords y c) := hxy ▸ h

theorem toWords_length (x c : Nat) : (Spec.Rsa.toWords x c).length = c := by
  simp [Spec.Rsa.toWords]

theorem mask_true' : mask true = BitVec.allOnes 64 := by decide
theorem mask_false' : mask false = 0 := by decide

/-- The words at `p`, each a word of `ws` and'ed with `mask b`. -/
theorem wordsAt_masked {m : Mem} {p : Addr} {L : Nat} {ws : List (BitVec 64)} {b : Bool} (hL : ws.length = L)
    (h : ∀ i (hi : i < L), Bignum.word m p (8 * i) = ws[i] &&& mask b) :
    Spec.Rsa.wordsAt m p L = if b then ws else List.replicate L 0 := by
  apply List.ext_getElem
  · cases b <;> simp [Spec.Rsa.wordsAt, hL]
  · intro i h₁ h₂
    simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range] at h₁
    have := h i h₁
    simp only [Bignum.word, off] at this
    cases b
    · rw [mask_false'] at this; simp [Spec.Rsa.wordsAt, this]
    · rw [mask_true', BitVec.and_allOnes] at this; simp [Spec.Rsa.wordsAt, this]

/-- A change that keeps the words past the arrays but those at `[o, o + n)`. -/
def KeepsD (B : Addr) (w Z o n : Nat) (m m' : Mem) : Prop :=
  ∀ d (xs : List (BitVec 64)), slot w 8 ≤ d → (d + 8 * xs.length ≤ o ∨ o + n ≤ d) → d + 8 * xs.length ≤ Z →
    DWords m B d xs → DWords m' B d xs

theorem KeepsD.trans {B : Addr} {w Z o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : KeepsD B w Z o n m₁ m₂)
    (h₂ : KeepsD B w Z o n m₂ m₃) : KeepsD B w Z o n m₁ m₃ :=
  fun d xs h₀ hd hZ hw => h₂ d xs h₀ hd hZ (h₁ d xs h₀ hd hZ hw)

theorem KeepsD.of_arrays {B : Addr} {w Z o n : Nat} {js : List Nat} {m m' : Mem} (ha : Arrays B w js m m')
    (hjs : ∀ j ∈ js, j < 8) (hn : B.toNat + Z ≤ 2 ^ 64) : KeepsD B w Z o n m m' :=
  fun _ _ h₀ _ hZ hw => hw.arrays ha hjs h₀ (by omega)

theorem KeepsD.of_outside {B : Addr} {w Z o n : Nat} {m m' : Mem} (ho : Outside B o n m m')
    (hn : B.toNat + Z ≤ 2 ^ 64) : KeepsD B w Z o n m m' :=
  fun _ _ _ hd hZ hw => hw.frame ho hd (by omega)

/-- What an offset's code `off` does in `copyOut off j`, from the context:
`rbx` to word `e` past the arrays and `r12 := c`. -/
def OffOk (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N : Nat) (offI : List Instr) (e c : Nat) :
    Prop :=
  ∀ t, KCtx s t B Z w minv N → ∀ u : State, Keep [.rax, .rbx, .r12] t u → u.mem = t.mem →
    u.gpr .rbx = off B (slot w 8) → u.gpr .r12 = BitVec.ofNat 64 w →
    WP isa (.block offI) u fun u' => u'.gpr .rbx = off B (slot w 8 + 8 * e) ∧
      u'.gpr .r12 = BitVec.ofNat 64 c ∧ u'.mem = u.mem ∧ Keep [.rax, .rbx, .r12] u u'

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

/-- One value: the modulus `bs` into `aM`, the accumulator `A` (`acc`),
`A mod bs` (`reduce cnt`), and its `c` words to word `e` past the arrays. -/
theorem redPhaseK (h : KCtx s t B Z w minv N) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hsp' : sp ≠ sMask)
    (hsl' : sl ≠ sMask) {p : Addr} {bs : List Byte} (hp : Bignum.word s.mem B (8 * sp) = p)
    (hl : Bignum.word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length) (hsrc : Src s B Z p bs)
    (hk1 : 1 ≤ bs.length) (hkw : bs.length ≤ 8 * w)
    {acc : List (Prog isa)} {cnt : List Instr} {L A : Nat} (hacc0 : acc ≠ [])
    (hacc : ∀ u, KCtx s u B Z w minv N → WP isa (seqs acc) u fun u' => KCtx s u' B Z w minv N ∧
      wv u'.mem B (slot w aAcc) L = A ∧ Arrays B w [aAcc, aTmp] u.mem u'.mem)
    (hred : ∀ u, KCtx s u B Z w minv N → WP isa (seqs (reduce cnt)) u fun u' => KCtx s u' B Z w minv N ∧
      (0 < wv u.mem B (slot w aM) w →
        wv u'.mem B (slot w aR) w = wv u.mem B (slot w aAcc) L % wv u.mem B (slot w aM) w) ∧
      Arrays B w [aR, aX, aT] u.mem u'.mem)
    {offI : List Instr} {e c : Nat} (hoff : OffOk s B Z w minv N offI e c) (hc : 1 ≤ c) (hcw : c ≤ w)
    (he : slot w 8 + 8 * (e + c) ≤ Z) :
    WP isa (seqs (loadNum aM sp sl ++ acc ++ reduce cnt ++ copyOut offI aR)) t fun t' =>
      KCtx s t' B Z w minv N ∧
      (0 < Spec.Rsa.os2ip bs →
        DWords t'.mem B (slot w 8 + 8 * e) (Spec.Rsa.toWords (A % Spec.Rsa.os2ip bs) c)) ∧
      KeepsD B w Z (slot w 8 + 8 * e) (8 * c) t.mem t'.mem ∧
      Bignum.word t'.mem B (8 * sMask) = Bignum.word t.mem B (8 * sMask) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  simp only [List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [copyOut]) (WP.mono (loadK h (j := aM) (by decide) (by decide) (by decide)
    hsp hsl hsp' hsl' hp hl hsrc hk1 hkw) fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa hacc0 (by simp [reduce]) (WP.mono (hacc t₁ h₁) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [← Arrays.wv_other a₂ (by decide) (by decide) hZ hn] at v₁
  refine wsa (by simp [reduce]) (by simp [copyOut]) (WP.mono (hred t₂ h₂) fun t₃ ⟨h₃, v₃, a₃⟩ => ?_)
  refine WP.mono (copyOutK h₃ (j := aR) (by decide) (hoff t₃ h₃) hc (by omega) he) fun t₄ ⟨h₄, c₄, o₄⟩ => ?_
  refine ⟨h₄, fun hb => DWords.of_copy c₄ (v₃ (by rw [v₁]; exact hb)) hcw |>.congr_toWords (by rw [v₂, v₁]), ?_, ?_⟩
  · exact (((KeepsD.of_arrays a₁ (by decide) hn).trans (KeepsD.of_arrays a₂ (by decide) hn)).trans
      (KeepsD.of_arrays a₃ (by decide) hn)).trans (KeepsD.of_outside o₄ hn)
  · have := hdr_lt_slot w 8 (show sMask < 32 by decide)
    rw [o₄.word (Or.inl (by omega)) (by omega),
      Arrays.mask_eq a₃ hn hZ, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ]

theorem offNil : OffOk s B Z w minv N [] 0 w := fun _ _ u _ _ hbx h12 =>
  WP.mono (WP.keep [] (Q := fun u' => u'.gpr .rbx = off B (slot w 8 + 8 * 0) ∧
      u'.gpr .r12 = BitVec.ofNat 64 w ∧ u'.mem = u.mem) (by xrun [hbx, h12, Nat.mul_zero, Nat.add_zero]) rfl)
    fun _ ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d.mono (by decide)⟩

theorem offSkip : OffOk s B Z w minv N skipW w w := fun _ _ u _ _ hbx h12 =>
  WP.mono (skipW_ok hbx h12) fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d.mono (by decide)⟩

theorem offPrime {pl : Nat} (hpl : Bignum.word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (h1 : 1 ≤ pl)
    (hpw : pl < 2 ^ 32) : OffOk s B Z w minv N (skipW ++ skipW ++ primeW sPlen) (2 * w)
      (Spec.Rsa.primeWords pl) := fun t h u ku hmu hbx h12 => by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (skipW_ok hbx h12) fun u₁ ⟨hbx₁, h12₁, hm₁, k₁⟩ => ?_
  refine WP.mono (skipW_ok hbx₁ h12₁) fun u₂ ⟨hbx₂, h12₂, hm₂, k₂⟩ => ?_
  have k := (ku.trans k₁).trans k₂
  refine WP.mono (primeW_ok ((k.gpr (by decide)).trans h.good.rdi)
    (by rw [k.2.1, k.2.2]; exact h.ld (by decide))
    (by rw [hm₂, hm₁, hmu, h.hdr sPlen (by decide) (by decide)]; exact hpl) h1 hpw) fun u' ⟨h12', hm', k'⟩ => ?_
  refine ⟨?_, h12', by rw [hm', hm₂, hm₁], ((k₁.trans k₂).trans k').mono (by decide)⟩
  rw [(k'.gpr (by decide)).trans hbx₂, show slot w 8 + 8 * w + 8 * w = slot w 8 + 8 * (2 * w) by omega]

theorem offPrime2 {pl ql : Nat} (hpl : Bignum.word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hql : Bignum.word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hp1 : 1 ≤ pl) (hpw : pl < 2 ^ 32)
    (hq1 : 1 ≤ ql) (hqw : ql < 2 ^ 32) :
    OffOk s B Z w minv N (skipW ++ skipW ++ primeW sPlen ++ skipW ++ primeW sQlen)
      (2 * w + Spec.Rsa.primeWords pl) (Spec.Rsa.primeWords ql) := fun t h u ku hmu hbx h12 => by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (offPrime hpl hp1 hpw t h u ku hmu hbx h12) fun u₁ ⟨hbx₁, h12₁, hm₁, k₁⟩ => ?_
  refine WP.mono (skipW_ok hbx₁ h12₁) fun u₂ ⟨hbx₂, h12₂, hm₂, k₂⟩ => ?_
  have k := (ku.trans k₁).trans k₂
  refine WP.mono (primeW_ok ((k.gpr (by decide)).trans h.good.rdi)
    (by rw [k.2.1, k.2.2]; exact h.ld (by decide))
    (by rw [hm₂, hm₁, hmu, h.hdr sQlen (by decide) (by decide)]; exact hql) hq1 hqw) fun u' ⟨h12', hm', k'⟩ => ?_
  refine ⟨?_, h12', by rw [hm', hm₂, hm₁], ((k₁.trans k₂).trans k').mono (by decide)⟩
  rw [(k'.gpr (by decide)).trans hbx₂, show slot w 8 + 8 * (2 * w) + 8 * Spec.Rsa.primeWords pl =
    slot w 8 + 8 * (2 * w + Spec.Rsa.primeWords pl) by omega]

/-- `maskOut`: the `L` words past the arrays, and'ed with `sMask`, to `pre`. -/
theorem maskOutK (h : KCtx s t B Z w minv N) {op : Addr} {L : Nat} {b : Bool}
    (hO : Bignum.word s.mem B (8 * sE) = op)
    (hLw : Bignum.word s.mem B (8 * sElen) = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL2 : L < 2 ^ 31)
    (hLZ : slot w 8 + 8 * L ≤ Z) (hm : Bignum.word t.mem B (8 * sMask) = mask b)
    (hpw : ∀ i < L, InRegions t.wr (off op (8 * i)) 8)
    (hps : ∀ i < 8 * L, Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (seqs maskOut) t fun t' =>
      (∀ i < L, Bignum.word t'.mem op (8 * i) = Bignum.word t.mem B (slot w 8 + 8 * i) &&& mask b) ∧
      (∀ x, 8 * L ≤ ofs op x → t'.mem x = t.mem x) ∧ Keep mmRegs t t' := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have hsep : ∀ x, ofs B x < Z → 8 * L ≤ ofs op x := fun x hx => le_ofs_of_sep hps hx
  show WP isa (.seq (.block _) maskWords) t _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (dBase_ok h.good hZ) fun u₁ ⟨hbx₁, h12₁, hm₁, k₁⟩ => ?_
  have hdi₁ : u₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.good.rdi
  have hl₁ : ∀ i < 32, InRegions (u₁.rd ++ u₁.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₁.2.1, k₁.2.2]; exact h.ld hi
  refine WP.mono (WP.keep [.rsi, .rbx, .r12, .rbp] (Q := fun u => u.gpr .rsi = off B (slot w 8) ∧
      u.gpr .rbx = op ∧ u.gpr .r12 = BitVec.ofNat 64 L ∧ u.gpr .rbp = mask b ∧ u.mem = t.mem) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hl₁ sE (by decide), hl₁ sElen (by decide),
      hl₁ sMask (by decide), hbx₁, hm₁, h.hdr sE (by decide) (by decide), hO,
      h.hdr sElen (by decide) (by decide), hLw, hm]) rfl) fun u₂ ⟨⟨hsi₂, hbx₂, h12₂, hbp₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (maskWords_ok (D := op) (eD := 0) (n := L) hsi₂ (by rw [hbx₂]; simp [off]) h12₂ hbp₂ hL1 (by omega) (by omega)
    (fun j hj => by rw [k12.2.1, k12.2.2]; exact h.good.scr.ld (by omega))
    (fun j hj => by rw [k12.2.2, Nat.zero_add]; exact hpw j hj)
    (fun j hj b hb => Or.inr (by rw [Nat.zero_add]; exact hsep _ (by rw [ofs_off B (by omega)]; omega))))
    fun t' ⟨hw', ho', k'⟩ => ?_
  rw [hm₂] at hw' ho'
  refine ⟨fun i hi => by have := hw' i hi; rwa [Nat.zero_add] at this,
    fun x hx => ho' x (Or.inr (by omega)), ((k12.trans k').mono (by decide))⟩

end

/-- `Good` after code that changes only memory outside the working space. -/
theorem goodOfInScr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hi : ∀ x, ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = B) : Good t B Z w minv := by
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have hw : ∀ i < 32, Bignum.word t.mem B (8 * i) = Bignum.word s.mem B (8 * i) := fun i hi' =>
    Mem.readW_congr fun b hb => hi _ (by rw [ofs_off B (d := 8 * i) (i := b) (by omega)]; omega)
  exact ⟨hg.scr.congr hwr, hdi, ⟨by rw [hw sW (by decide)]; exact hg.hdr.hw,
    by rw [hw sMinv (by decide)]; exact hg.hdr.hminv,
    fun j hj => by rw [hw (sArr j) (by unfold sArr; omega)]; exact hg.hdr.harr j hj⟩⟩

theorem DWords.congr_d {m : Mem} {B : Addr} {d d' : Nat} {xs : List (BitVec 64)} (h : DWords m B d xs)
    (hd : d = d') : DWords m B d' xs := hd ▸ h

/-- What `pre` holds when `p q = n`, for a modulus of `k` octets: `n`,
`R² mod n`, `R_p mod p` and `R_q mod q`. -/
def preWs (k : Nat) (nb pb qb : List Byte) : List (BitVec 64) :=
  Spec.Rsa.toWords (Spec.Rsa.os2ip nb) ((k + 7) / 8) ++
    Spec.Rsa.toWords (2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb) ((k + 7) / 8) ++
    Spec.Rsa.toWords (2 ^ (64 * Spec.Rsa.primeWords pb.length) % Spec.Rsa.os2ip pb)
      (Spec.Rsa.primeWords pb.length) ++
    Spec.Rsa.toWords (2 ^ (64 * Spec.Rsa.primeWords qb.length) % Spec.Rsa.os2ip qb)
      (Spec.Rsa.primeWords qb.length)

theorem preMain_eq : Impl.Rsa.X86_64.PrivPre.main = seqs (([.block VG.Impl.Rsa.X86_64.head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] : List (Prog isa)) ++
    ((loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ VG.Impl.Rsa.X86_64.Crt.eqCheck) ++
    (copyOut [] aN ++
    ((loadNum aM sD sDlen ++ accTop ++ reduce cntXR ++ copyOut skipW aR) ++
    ((loadNum aM sP sPlen ++ accPrime sPlen ++ reduce cntE ++ copyOut (skipW ++ skipW ++ primeW sPlen) aR) ++
    ((loadNum aM sQ sQlen ++ accPrime sQlen ++ reduce cntE ++
      copyOut (skipW ++ skipW ++ primeW sPlen ++ skipW ++ primeW sQlen) aR) ++
    (maskOut ++
    ([.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] :
      List (Prog isa))))))))) := by
  simp only [Impl.Rsa.X86_64.PrivPre.main, List.append_assoc]

/-- `main`, for a valid modulus: `pre` holds `preWs` if `p q = n` and zeros
otherwise, which is returned as 1 or 0, and the saved registers restored. -/
theorem preMain_ok {s : State} {B : Addr} {Z k : Nat} {np pp pq op : Addr} {nb pb qb : List Byte} {ev L : Nat}
    (hp : MainPre s B Z k np np pp pq pp pq pp nb nb pb qb pb qb pb ev)
    (hO : Bignum.word s.mem B (8 * sE) = op) (hLw : Bignum.word s.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : L = Spec.Rsa.privatePrecomputedWords k pb.length qb.length)
    (hpw : ∀ i < L, InRegions s.wr (off op (8 * i)) 8)
    (hps : ∀ i < 8 * L, Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa Impl.Rsa.X86_64.PrivPre.main s fun t =>
      Spec.Rsa.wordsAt t.mem op L = (if Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb then
        preWs k nb pb qb else List.replicate L 0) ∧
      t.gpr .rax = BitVec.ofNat 64 (decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = Bignum.word s.mem B (8 * i)) ∧
      (∀ x, Z ≤ ofs B x → 8 * L ≤ ofs op x → t.mem x = s.mem x) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Keep mmRegs s t := by
  have := hp.k1
  have := hp.k2
  have := hp.pl1
  have := hp.pl2
  have := hp.ql1
  have := hp.ql2
  have hn := hp.scr.nowrap
  have hzk := hp.zk
  have hk8 : k ≤ 8 * ((k + 7) / 8) := by omega
  have hw8 : 8 ≤ (k + 7) / 8 := by omega
  have hwp : Spec.Rsa.primeWords pb.length ≤ (k + 7) / 8 := by
    unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega
  have hwq : Spec.Rsa.primeWords qb.length ≤ (k + 7) / 8 := by
    unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega
  have hwp2 : 2 ≤ Spec.Rsa.primeWords pb.length := by unfold Spec.Rsa.primeWords; omega
  have hwq2 : 2 ≤ Spec.Rsa.primeWords qb.length := by unfold Spec.Rsa.primeWords; omega
  have hLv : L = 2 * ((k + 7) / 8) + Spec.Rsa.primeWords pb.length + Spec.Rsa.primeWords qb.length := by
    rw [hL]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; rfl
  have hSZ : slot ((k + 7) / 8) 8 + 8 * L ≤ Z := by rw [hLv]; unfold slot hdrBytes; omega
  rw [preMain_eq]
  refine wsa (by simp) (by simp [loadNum]) (WP.mono (setupK_ok hp)
    fun t₀ ⟨minv, h₀, m₀, hw, in₀, rd₀, wr₀, k₀⟩ => ?_)
  have sr : ∀ {p : Addr} {bs : List Byte}, Src s B Z p bs → Src t₀ B Z p bs := fun h => h.congr in₀ rd₀ wr₀
  -- `p q = n`
  refine wsa (by simp [loadNum]) (by simp [copyOut]) (WP.mono (pqN_ok h₀ m₀
    (by rw [hw sP (by decide) (by decide)]; exact hp.hP) (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl)
    (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ) (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl)
    (sr hp.srP) (sr hp.srQ) hp.pl1 (by omega) hp.ql1 (by omega)) fun t₂ ⟨h₂, m₂⟩ => ?_)
  -- `n`
  refine wsa (by simp [copyOut]) (by simp [loadNum]) (WP.mono (copyOutK h₂ (j := aN) (by decide)
    (offNil t₂ h₂) (by omega) (by omega) (by omega)) fun t₃ ⟨h₃, c₃, o₃⟩ => ?_)
  have D₁ : DWords t₃.mem B (slot ((k + 7) / 8) 8 + 8 * 0)
      (Spec.Rsa.toWords (Spec.Rsa.os2ip nb) ((k + 7) / 8)) := DWords.of_copy c₃ h₂.n (Nat.le_refl _)
  have M₃ : Bignum.word t₃.mem B (8 * sMask) = Bignum.word t₂.mem B (8 * sMask) :=
    o₃.word (Or.inl (by have := hdr_lt_slot ((k + 7) / 8) 8 (show sMask < 32 by decide); omega))
      (by have := hdr_lt_slot ((k + 7) / 8) 8 (show sMask < 32 by decide); omega)
  -- `R² mod n`
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (redPhaseK h₃ (sp := sD) (sl := sDlen)
    (by decide) (by decide) (by decide) (by decide) (by rw [hw sD (by decide) (by decide)]; exact hp.hD)
    (by rw [hw sDlen (by decide) (by decide)]; exact hp.hDl) (sr hp.srD) (by rw [hp.nl]; omega) (by rw [hp.nl]; exact hk8)
    (by simp [accTop]) (fun u hu => accTopK hu (by omega)) (fun u hu => reduceXRK hu) offSkip (by omega)
    (Nat.le_refl _) (by omega)) fun t₄ ⟨h₄, D₂, K₄, M₄⟩ => ?_)
  -- `R_p mod p`
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (redPhaseK h₄ (sp := sP) (sl := sPlen)
    (by decide) (by decide) (by decide) (by decide) (by rw [hw sP (by decide) (by decide)]; exact hp.hP)
    (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl) (sr hp.srP) hp.pl1 (by omega)
    (by simp [accPrime]) (fun u hu => accPrimeK hu (sl := sPlen) (by decide) (by decide)
      (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl) hp.pl1 (by omega) (by omega))
    (fun u hu => reduceEK hu) (offPrime (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl) hp.pl1
      (by omega)) (by omega) hwp (by omega)) fun t₅ ⟨h₅, D₃, K₅, M₅⟩ => ?_)
  -- `R_q mod q`
  refine wsa (by simp [loadNum]) (by simp [maskOut]) (WP.mono (redPhaseK h₅ (sp := sQ) (sl := sQlen)
    (by decide) (by decide) (by decide) (by decide) (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ)
    (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl) (sr hp.srQ) hp.ql1 (by omega)
    (by simp [accPrime]) (fun u hu => accPrimeK hu (sl := sQlen) (by decide) (by decide)
      (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl) hp.ql1 (by omega) (by omega))
    (fun u hu => reduceEK hu) (offPrime2 (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl)
      (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl) hp.pl1 (by omega) hp.ql1 (by omega))
    (by omega) hwq (by omega)) fun t₆ ⟨h₆, D₄, K₆, M₆⟩ => ?_)
  have hZ := h₆.hZ
  have m₆ : Bignum.word t₆.mem B (8 * sMask) =
      mask (true && decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)) := by
    rw [M₆, M₅, M₄, M₃, m₂]
  -- The words past the arrays, when `p q = n`.
  have hD : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb →
      DWords t₆.mem B (slot ((k + 7) / 8) 8) (preWs k nb pb qb) := fun hpq => by
    have hN1 : 1 < Spec.Rsa.os2ip nb := (valid_facts hp.mv (by omega)).2.1
    have hp0 : 0 < Spec.Rsa.os2ip pb := Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hpq; omega
    have hq0 : 0 < Spec.Rsa.os2ip qb := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hpq; omega
    have E₁ := K₆ _ _ (by omega) (Or.inl (by rw [toWords_length]; omega)) (by rw [toWords_length]; omega)
      (K₅ _ _ (by omega) (Or.inl (by rw [toWords_length]; omega)) (by rw [toWords_length]; omega)
        (K₄ _ _ (by omega) (Or.inl (by rw [toWords_length]; omega)) (by rw [toWords_length]; omega) D₁))
    have E₂ := K₆ _ _ (by omega) (Or.inl (by rw [toWords_length]; omega)) (by rw [toWords_length]; omega)
      (K₅ _ _ (by omega) (Or.inl (by rw [toWords_length]; omega)) (by rw [toWords_length]; omega)
        (D₂ (by omega)))
    have E₃ := K₆ _ _ (by omega) (Or.inl (by rw [toWords_length]; omega)) (by rw [toWords_length]; omega)
      (D₃ hp0)
    have E₄ := D₄ hq0
    refine ((((E₁.congr_d (by omega)).append (E₂.congr_d (by rw [toWords_length]))).append
      (E₃.congr_d (by simp only [List.length_append, toWords_length]; omega))).append
      (E₄.congr_d (by simp only [List.length_append, toWords_length]; omega)))
  have hlen : (preWs k nb pb qb).length = L := by simp only [preWs, List.length_append, toWords_length]; omega
  -- The words, masked, to `pre`.
  refine wsa (by simp [maskOut]) (by simp) (WP.mono (maskOutK h₆ (b := decide (Spec.Rsa.os2ip pb *
      Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)) (by rw [hw sE (by decide) (by decide)]; exact hO)
    (by rw [hw sElen (by decide) (by decide)]; exact hLw) (by omega) (by omega) hSZ
    (by rw [m₆, Bool.true_and]) (fun i hi => by rw [h₆.wr, wr₀]; exact hpw i hi) hps)
    fun t₇ ⟨hw₇, hf₇, k₇⟩ => ?_)
  have hin₇ : ∀ x, ofs B x < Z → t₇.mem x = t₆.mem x := fun x hx => hf₇ x (le_ofs_of_sep hps hx)
  have hword₇ : ∀ d, d + 8 ≤ Z → Bignum.word t₇.mem B d = Bignum.word t₆.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hin₇ _ (by rw [ofs_off B (d := d) (i := b) (by omega)]; omega)
  have hg₇ : Good t₇ B Z ((k + 7) / 8) minv := goodOfInScr h₆.good hZ hin₇ k₇.2.2
    ((k₇.gpr (by decide)).trans h₆.good.rdi)
  refine WP.mono (outK_ok hg₇ hZ (c := decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb))
    (by rw [hword₇ _ (by have := hdr_lt_slot ((k + 7) / 8) 8 (show sMask < 32 by decide); omega), m₆,
      Bool.true_and])) fun t ⟨hax, hsv, hm, kk⟩ => ⟨?_, hax, fun i hi => ?_, fun x hx hx' => ?_,
      kk.2.1.trans (k₇.2.1.trans (h₆.rd.trans rd₀)), kk.2.2.trans (k₇.2.2.trans (h₆.wr.trans wr₀)),
      (((k₀.trans h₆.keep).trans k₇).trans kk).mono (by decide)⟩
  · rw [hm, wordsAt_masked (b := decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)) hlen
      fun i hi => by
        rw [hw₇ i hi]
        by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
        · rw [hD hpq i (by omega), decide_eq_true hpq, mask_true', BitVec.and_allOnes]
        · rw [decide_eq_false hpq, mask_false']; simp]
    by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb <;> simp [hpq]
  · rw [hsv i hi, hword₇ _ (by have := hdr_lt_slot ((k + 7) / 8) 8 (show i < 32 by omega); omega),
      h₆.hdr i (by omega) (by unfold sMask sFn; omega)]
    exact hw i (by omega) (by revert hi; revert i; decide)
  · rw [hm, hf₇ x hx', h₆.ins x hx, in₀ x hx]

end VG.Proof.Rsa.X86_64.Key
