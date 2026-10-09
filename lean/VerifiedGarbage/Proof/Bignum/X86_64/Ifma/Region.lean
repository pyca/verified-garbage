import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Pre
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: a prime's region

`region` fills prime `p`'s region of the IFMA
area from its workspace: the modulus, `2^dbls R_X mod X`, the base and
`R_X` in the stride layout (`arr52_ok`), `k₀` (`k0St_ok`), the last
multiplier, and the exponent's bytes after zeros (`eCopy_ok`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside wv)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (stMem stMem_outside word_stMem_other word_stMem limbN limbN_lt writeB_outside
  ofs_self writeB_self setWidth_byte' se_ofNat off_add)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## Stores of `rax` -/

theorem stRax_ok {C : Addr} {v : BitVec 64} :
    ∀ (ds : List Nat) (s : State), s.gpr .r11 = C → s.gpr .rax = v →
      (∀ d ∈ ds, InRegions s.wr (C + BitVec.ofNat 64 d) 8) →
      WP isa (.block (ds.map fun d => .store (at_ .r11 d) .rax)) s
        fun s' => s' = { s with mem := stMem s.mem C v ds }
  | [], s, _, _, _ => WP.block_nil rfl
  | d :: rest, s, hC, hv, hw => by
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off C d) v }, ?_, ?_⟩
    · simp only [exec, eaG', hC, hv, State.store64, hw d (List.mem_cons_self ..), ite_true, off]
    · exact WP.mono (stRax_ok rest _ hC hv fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => h

theorem map_store (f : Nat → Nat) (xs : List Nat) :
    xs.map (fun x => Instr.store (at_ .r11 (f x)) .rax) = (xs.map f).map (fun d => .store (at_ .r11 d) .rax) := by
  simp only [List.map_map, Function.comp_def]

/-! ## Arrays into the stride layout -/

/-- Array `j` of the prime's workspace `W` (`Aj`) into the limbs at `o` of
region `p` of the area `A`. -/
theorem arr52_ok (hl : LayOk l) {s : State} {W A Aj : Addr} {p j o : Nat} (hdi : s.gpr .rdi = W)
    (hH : ∀ i < 32, InRegions (s.rd ++ s.wr) (off W (8 * i)) 8) (hjs : VG.Impl.Bignum.X86_64.sArr j < 32)
    (hj : word s.mem W (8 * VG.Impl.Bignum.X86_64.sArr j) = Aj)
    (hA : word s.mem W (8 * sIfma) = A) (hc : l.D * p + o < 2 ^ 31)
    (hrd : ∀ i < l.W, InRegions (s.rd ++ s.wr) (Aj + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : ∀ k < l.L, InRegions s.wr (off A (l.D * p + o) + BitVec.ofNat 64 (l.off k)) 8)
    (hsep : ∀ m m' : Mem, Outside (off A (l.D * p + o)) 0 l.NB m m' → ∀ i < l.W,
      word m' Aj (8 * i) = word m Aj (8 * i)) :
    WP isa (.block (arr52 l p j o)) s fun s' =>
      (∀ k < l.L, word s'.mem (off A (l.D * p + o)) (l.off k) = BitVec.ofNat 64 (limbN (wv s.mem Aj 0 l.W) k)) ∧
      Outside (off A (l.D * p + o)) 0 l.NB s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] s s' ∧ s'.gpr .r12 = mask52 ∧
      s'.mxcsr = s.mxcsr := by
  unfold arr52
  rw [WP.block_append_iff]
  have l1 := hH _ hjs
  have l2 := hH sIfma (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rsi, .r11, .r12] (Q := fun t => t.gpr .rsi = Aj ∧
    t.gpr .r11 = off A (l.D * p + o) ∧ t.gpr .r12 = mask52 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, l1, l2, se_ofNat hc]
      and_intros
      · exact hj
      · exact congrArg (· + BitVec.ofNat 64 (l.D * p + o)) hA
      all_goals rfl) rfl) fun t ⟨⟨si, r11, r12, me, mx⟩, k⟩ => ?_
  refine WP.mono (to52_ok hl si r11 r12 (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi)
    (fun i hi => by rw [k.2.2]; exact hwr i hi) hsep) fun s' ⟨v, o', k', x'⟩ => ?_
  rw [me] at v o'
  exact ⟨v, o', (k.trans k').mono (by decide), by rw [k'.gpr (by decide)]; exact r12, x'.trans mx⟩

/-! ## `k₀`, zeros and the last multiplier -/

/-- `k₀ = minv mod 2⁵²` in the four quadwords at `oK0` of region `p` (`r11 := C`, its base). -/
theorem k0St_ok {s : State} {W A : Addr} {p : Nat} {minv : BitVec 64} (hdi : s.gpr .rdi = W)
    (hH : ∀ i < 32, InRegions (s.rd ++ s.wr) (off W (8 * i)) 8)
    (hA : word s.mem W (8 * sIfma) = A)
    (hm : word s.mem W (8 * VG.Impl.Bignum.X86_64.sMinv) = minv) (h12 : s.gpr .r12 = mask52)
    (hc : l.D * p < 2 ^ 31) (hk : l.oK0 + 32 < 2 ^ 31)
    (hwr : ∀ t < 4, InRegions s.wr (off A (l.D * p) + BitVec.ofNat 64 (l.oK0 + 8 * t)) 8) :
    WP isa (.block (k0St l p)) s fun s' =>
      (∀ t < 4, word s'.mem (off A (l.D * p)) (l.oK0 + 8 * t) = minv &&& mask52) ∧
      Outside (off A (l.D * p)) l.oK0 32 s.mem s'.mem ∧ s'.gpr .r11 = off A (l.D * p) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  unfold k0St
  rw [WP.block_append_iff]
  have l1 := hH sIfma (by decide)
  have l2 := hH VG.Impl.Bignum.X86_64.sMinv (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .r11] (Q := fun t =>
    t.gpr .r11 = off A (l.D * p) ∧ t.gpr .rax = minv &&& mask52 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, l1, l2, se_ofNat hc, h12]
      and_intros
      · exact congrArg (· + BitVec.ofNat 64 (l.D * p)) hA
      · exact congrArg (· &&& mask52) hm
      all_goals rfl) rfl) fun t ⟨⟨r11, ra, me, mx⟩, k⟩ => ?_
  have hlr : ∀ d ∈ (List.range 4).map (fun i => l.oK0 + 8 * i), l.oK0 ≤ d ∧ d + 8 ≤ l.oK0 + 32 := by
    simp only [List.mem_map, List.mem_range]; rintro _ ⟨i, hi, rfl⟩; omega_using [hi]
  rw [map_store (fun i => l.oK0 + 8 * i)]
  refine WP.mono (stRax_ok _ t r11 ra fun d hd => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [k.2.2]; exact hwr i (List.mem_range.mp hi)) fun s' hs' => ?_
  subst hs'
  refine ⟨fun i hi' => ?_, ?_, r11, k, mx⟩
  · exact word_stMem _ _ _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩) (fun d hd => by
      obtain ⟨i', hi'', rfl⟩ := List.mem_map.mp hd
      rw [List.mem_range] at hi''
      by_cases e : i' = i
      · exact .inl (by rw [e])
      · exact .inr (by omega_using [e])) (fun d hd => by have := hlr d hd; omega_using [hk, this])
  · rw [← me]; exact stMem_outside _ _ _ (by omega_using [hk]) _ hlr

/-- Zeros in the `W` quadwords at `oE` (`r11 = C`). -/
theorem eZero_ok {s : State} {C : Addr} (hC : s.gpr .r11 = C) (hE : l.oE + l.E < 2 ^ 31)
    (hwr : ∀ i < l.W, InRegions s.wr (C + BitVec.ofNat 64 (l.oE + 8 * i)) 8) :
    WP isa (.block (eZero l)) s fun s' =>
      (∀ i < l.W, word s'.mem C (l.oE + 8 * i) = 0) ∧ Outside C l.oE l.E s.mem s'.mem ∧ s'.gpr .rax = 0 ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hEW : l.E = 8 * l.W := rfl
  rw [show eZero l = [.mov32 .rax (.imm 0)] ++
    (List.range l.W).map (fun i => .store (at_ .r11 (l.oE + 8 * i)) .rax) from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = 0 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by xrun; and_intros; all_goals rfl) rfl)
    fun t ⟨⟨ra, me, mx⟩, k⟩ => ?_
  have r11 : t.gpr .r11 = C := by rw [k.gpr (by decide)]; exact hC
  have hlr : ∀ d ∈ (List.range l.W).map (fun i => l.oE + 8 * i), l.oE ≤ d ∧ d + 8 ≤ l.oE + l.E := by
    simp only [List.mem_map, List.mem_range]; rintro _ ⟨i, hi, rfl⟩; omega_using [hEW, hi]
  rw [map_store (fun i => l.oE + 8 * i)]
  refine WP.mono (stRax_ok _ _ r11 ra fun d hd => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [k.2.2]; exact hwr i (List.mem_range.mp hi)) fun s' hs' => ?_
  subst hs'
  refine ⟨fun i hi' => ?_, by rw [← me]; exact stMem_outside _ _ _ (by omega_using [hE]) _ hlr, ra, k, mx⟩
  exact word_stMem _ _ _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩) (fun d hd => by
    obtain ⟨i', hi'', rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hi''
    by_cases e : i' = i
    · exact .inl (by rw [e])
    · exact .inr (by omega_using [e])) (fun d hd => by have := hlr d hd; omega_using [hE, this])

/-- `q`'s last multiplier: 1, in the limbs at `oFin` (`r11 = C`, `rax = 0`). -/
theorem finOne_ok (hl : LayOk l) {s : State} {C : Addr} (hC : s.gpr .r11 = C) (ha : s.gpr .rax = 0)
    (hF : l.oFin + l.NB < 2 ^ 31)
    (hwr : ∀ j < l.L, InRegions s.wr (C + BitVec.ofNat 64 (l.oFin + l.off j)) 8) :
    WP isa (.block (finOne l)) s fun s' =>
      (∀ j < l.L, word s'.mem C (l.oFin + l.off j) = BitVec.ofNat 64 (limbN 1 j)) ∧
      Outside C l.oFin l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hL0 : 0 < l.L := by have := hl.bounds; simp only [Lay.L]; omega_using [this]
  unfold finOne
  rw [WP.block_append_iff, map_store (fun j => l.oFin + l.off j)]
  refine WP.mono (stRax_ok _ _ hC ha fun d hd => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    exact hwr j (List.mem_range.mp hj)) fun t ht => ?_
  subst ht
  have h0 : InRegions s.wr (C + BitVec.ofNat 64 l.oFin) 8 := by
    have := hwr 0 hL0; rwa [show l.off 0 = 0 by simp [Lay.off], Nat.add_zero] at this
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t' =>
    t'.mem = (stMem s.mem C 0 ((List.range l.L).map fun j => l.oFin + l.off j)).writeW
      (off C l.oFin) (1 : BitVec 64) ∧ t'.mxcsr = s.mxcsr) (by
      xrun [eaG', hC, h0]
      and_intros
      all_goals rfl) rfl) fun s' ⟨⟨me, mx⟩, k⟩ => ?_
  have hF' : ∀ j < l.L, l.oFin + l.off j + 8 ≤ l.oFin + l.NB := fun j hj => by
    have := off_lt hl hj; omega_using [this]
  refine ⟨fun j hj => ?_, ?_, ⟨fun r hr => k.gpr hr, k.2.1, k.2.2⟩, mx⟩
  · rw [me]
    by_cases e : j = 0
    · subst e
      rw [show l.off 0 = 0 by simp [Lay.off], Nat.add_zero]
      exact VG.Proof.Bignum.word_writeW_self _ _ _ _
    · have hs := off_sep hl (j := 0) (q := j) hL0 hj e
      have h00 : l.off 0 = 0 := by simp [Lay.off]
      rw [h00] at hs
      rw [(writeW_outside _ C _ (by omega_using [hF])).word (.inr (by omega_using [hs]))
        (by have := hF' j hj; omega_using [hF, this])]
      rw [word_stMem _ _ _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          rw [List.mem_range] at hj'
          by_cases e' : j' = j
          · exact .inl (by rw [e'])
          · exact .inr (by have := off_sep hl hj hj' e'; omega_using [this]))
        (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          have := hF' j' (List.mem_range.mp hj'); omega_using [hF, this])]
      unfold limbN
      rw [Nat.div_eq_of_lt (Nat.one_lt_two_pow (by
        intro h; apply e; have : j = 0 := by omega_using [h]
        exact this))]
      rfl
  · rw [me]
    exact (stMem_outside _ _ _ (by omega_using [hF]) _ fun d hd => by
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
      exact ⟨by omega_using [], hF' j' (List.mem_range.mp hj')⟩).trans
      ((writeW_outside _ C _ (by omega_using [hF])).mono (by omega_using []) (by have := NB_le hl; omega_using [this]))

/-! ## The exponent's bytes -/

/-- The copy after `j` bytes. -/
structure CpInv (s₀ t : State) (C ep : Addr) (L : Nat) (eb : List Byte) (hL : eb.length = L) (j : Nat) :
    Prop where
  si : t.gpr .rsi = ep + BitVec.ofNat 64 j
  di : t.gpr .r11 = C + BitVec.ofNat 64 j
  cx : t.gpr .rcx = BitVec.ofNat 64 (L - j)
  bytes : ∀ i (h : i < L), i < j → t.mem (C + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, h])
  out : Outside C 0 j s₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .r11] s₀ t
  mx : t.mxcsr = s₀.mxcsr

theorem cpStep_ok {s₀ t : State} {C ep : Addr} {L : Nat} {eb : List Byte} {hL : eb.length = L} {j : Nat}
    (hj : j < L) (hL2 : L < 2 ^ 31) (hI : CpInv s₀ t C ep L eb hL j)
    (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < L), s₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, h]))
    (hwr : ∀ i < L, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1)
    (hsep : ∀ m m' : Mem, Outside C 0 L m m' → ∀ i < L,
      m' (ep + BitVec.ofNat 64 i) = m (ep + BitVec.ofNat 64 i)) :
    WP isa (.block [.movzx8 .rax (VG.Impl.Bignum.X86_64.at0 .rsi), .store8 (VG.Impl.Bignum.X86_64.at0 .r11) .rax,
      .alu .add .rsi (.imm 1), .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) t fun t' =>
      t'.zf = some (decide (j + 1 = L)) ∧ CpInv s₀ t' C ep L eb hL (j + 1) := by
  have hr : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hw : InRegions t.wr (C + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwr j hj
  have hb : t.mem (ep + BitVec.ofNat 64 j) = eb[j]'(by omega_using [hL, hj]) := by
    rw [hsep _ _ (hI.out.mono (Nat.le_refl _) (by omega_using [hj])) j hj]; exact hval j hj
  have e0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => BitVec.add_zero x
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t' =>
    t'.gpr .rsi = ep + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .r11 = C + BitVec.ofNat 64 (j + 1) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (L - (j + 1)) ∧ t'.zf = some (decide (j + 1 = L)) ∧
      t'.mem = t.mem.writeW (C + BitVec.ofNat 64 j) (eb[j]'(by omega_using [hL, hj])) ∧ t'.mxcsr = t.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.at0, hI.si, hI.di, hI.cx, e0, hr, hw, hb]
      have e1 : BitVec.ofNat 64 (L - j) - 1 = BitVec.ofNat 64 (L - (j + 1)) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_using [hj])]
        congr 1
      and_intros
      · rw [BitVec.add_assoc, ofNat_add_one]
      · rw [BitVec.add_assoc, ofNat_add_one]
      · exact e1
      · rw [e1]
        by_cases h : j + 1 = L
        · simp only [h, Nat.sub_self, decide_true]; rfl
        · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
          intro h'
          have := congrArg BitVec.toNat h'
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hL2])] at this
          change _ = 0 at this
          omega_using [hj, h, this]
      · rw [setWidth_byte']
      · rfl) rfl) fun t' ⟨⟨si, di, cx, zf, me, mx⟩, k⟩ => ⟨zf, si, di, cx, fun i hiL hi => ?_, ?_,
        (hI.keep.trans k).mono (by decide), mx.trans hI.mx⟩
  · have ow := writeB_outside t.mem C (d := j) (eb[j]'(by omega_using [hL, hj])) (by omega_using [hj, hL2])
    rw [me]
    by_cases e : i = j
    · subst e; exact (writeB_self _ _ _).trans rfl
    · rw [ow _ (by rw [ofs_self C (by omega_using [hL2, hiL])]; omega_using [e])]
      exact hI.bytes i hiL (by omega_using [hi, e])
  · rw [me]
    exact (hI.out.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeB_outside t.mem C (d := j) (eb[j]'(by omega_using [hL, hj])) (by omega_using [hj, hL2])).mono (by omega_using [])
        (by omega_using []))

/-- The exponent's `L` bytes (`eb`, at `ep`, the pointer and length in the
slots `sp` and `sl` of `n`'s workspace `B`) at the end of the `E` at `oE`
of the region at `C` (`r11`). -/
theorem eCopy_ok {s : State} {W B C ep : Addr} {L sp sl : Nat} {eb : List Byte} (hL : eb.length = L)
    (hL1 : 1 ≤ L) (hL2 : L ≤ l.E) (hE : l.oE + l.E < 2 ^ 31) (hdi : s.gpr .rdi = W) (hC : s.gpr .r11 = C)
    (hlk : InRegions (s.rd ++ s.wr) (off W (8 * VG.Impl.Rsa.X86_64.Crt.sLink)) 8)
    (hlv : word s.mem W (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = B)
    (hp : InRegions (s.rd ++ s.wr) (off B (8 * sp)) 8) (hl' : InRegions (s.rd ++ s.wr) (off B (8 * sl)) 8)
    (hpv : word s.mem B (8 * sp) = ep) (hlv' : word s.mem B (8 * sl) = BitVec.ofNat 64 L)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < L), s.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, h]))
    (hwr : ∀ i < L, InRegions s.wr (off C (l.oE + l.E - L) + BitVec.ofNat 64 i) 1)
    (hsep : ∀ m m' : Mem, Outside (off C (l.oE + l.E - L)) 0 L m m' → ∀ i < L,
      m' (ep + BitVec.ofNat 64 i) = m (ep + BitVec.ofNat 64 i)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (eCopy l sp sl)) s fun s' =>
      (∀ i (h : i < L), s'.mem (off C (l.oE + l.E - L) + BitVec.ofNat 64 i) = eb[i]'(by omega_using [hL, h])) ∧
      Outside (off C (l.oE + l.E - L)) 0 L s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  unfold eCopy
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t =>
    t.gpr .rsi = ep ∧ t.gpr .r11 = off C (l.oE + l.E - L) ∧ t.gpr .rcx = BitVec.ofNat 64 L ∧ t.mem = s.mem ∧
      t.mxcsr = s.mxcsr) (by
      have hlv₁ : s.mem.readW (off W (8 * VG.Impl.Rsa.X86_64.Crt.sLink)) 64 = B := hlv
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdi, hdrOff, hlk, hlv₁, hp, hl',
        se_ofNat hE]
      and_intros
      · exact hpv
      · rw [show s.mem.readW (off B (8 * sl)) 64 = BitVec.ofNat 64 L from hlv', hC,
          VG.Offset.add_ofNat_sub _ (by omega_using [hL2])]
      · exact hlv'
      all_goals rfl) rfl) fun s₁ ⟨⟨si, di, cx, me, mx⟩, k⟩ => ?_)
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  refine wp_upto (a := 0) (N := L) (by omega_using [hL1])
    (fun j t => CpInv s₁ t (off C (l.oE + l.E - L)) ep L eb hL j)
    (fun j _ hj t hI => cpStep_ok hj (by omega_using [hL2, hE]) hI (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi)
      (fun i hi => by rw [me]; exact hval i hi) (fun i hi => by rw [k.2.2]; exact hwr i hi) hsep)
    (fun t hI => ⟨fun i hi => hI.bytes i hi hi, by rw [← me]; exact hI.out, (k.trans hI.keep).mono (by decide),
      hI.mx.trans mx⟩) ⟨by rw [e0]; exact si, by rw [e0]; exact di, by rw [Nat.sub_zero]; exact cx,
      fun _ _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩

section
open VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## `2^dbls R_X mod X` -/

/-- The ranges `k1` writes in the prime's workspace. -/
def k1Ranges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx Public.aAcc, 8 * (wx + 2)), (slot wx Public.aTmp, 8 * (wx + 2)),
    (slot wx VG.Impl.Rsa.X86_64.Crt.aT, 8 * (wx + 2)), (8 * sCtr, 8)]

theorem W_bounds (hl : LayOk l) : 16 ≤ l.W ∧ l.W ≤ 32 := by rcases hl with rfl | rfl | rfl <;> decide

/-- `aT := 2³² [aY] mod X` in the prime's workspace `W`. -/
theorem k1_ok (hl : LayOk l) {s : State} {W : Addr} {wx : Nat} {minv : BitVec 64} {X : Nat}
    (hg : VG.Proof.Bignum.X86_64.Good s W (slot wx 8) wx minv) (hw2 : 2 ≤ wx) (hw' : wx < 2 ^ 31)
    (hN : wv s.mem W (slot wx Public.aN) wx = X) (hY : wv s.mem W (slot wx Public.aY) wx < X) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (k1 l)) s fun t =>
      wv t.mem W (slot wx VG.Impl.Rsa.X86_64.Crt.aT) wx = 2 ^ l.dbls * wv s.mem W (slot wx Public.aY) wx % X ∧
      Frm W (k1Ranges wx) s.mem t.mem ∧ Hdr t.mem W wx minv ∧ Keep mmRegs s t := by
  unfold k1
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega_using [hw2]) hw'
    (o := VG.Impl.Rsa.X86_64.Crt.aT) (a := Public.aY) (by decide) (by decide) (by decide))
    fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_)
  have hn := hg.scr.nowrap
  have lT := slot_le (w := wx) (show VG.Impl.Rsa.X86_64.Crt.aT < 8 by decide)
  have lN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have sTN := slot_sep (w := wx) (show VG.Impl.Rsa.X86_64.Crt.aT ≠ Public.aN by decide)
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ : wv s₁.mem W (slot wx Public.aN) wx = X := by rw [ho₁.wv (by omega_using [sTN]) (by omega_using [hn, lN])]; exact hN
  simp only [VG.Impl.Bignum.X86_64.seqs]
  have hdb : 1 ≤ l.dbls ∧ l.dbls < 2 ^ 31 := by rcases hl with rfl | rfl | rfl <;> decide
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 l.dbls ∧ t.mem = s₁.mem) (by
    xrun; and_intros
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [hdb]), Nat.mod_eq_of_lt (by omega_using [hdb])]) rfl)
    fun s₂ ⟨⟨cx₂, me₂⟩, k₂⟩ => ?_)
  have hg₂ : VG.Proof.Bignum.X86_64.Good s₂ W (slot wx 8) wx minv := by
    refine ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ?_⟩
    rw [me₂]; exact hg₁.hdr
  refine WP.mono (doubles_ok hg₂.scr hg₂.rdi hg₂.hdr (Nat.le_refl _) hw2 hw' (mo := Public.aN)
    (acc := Public.aAcc) (tmp := Public.aTmp) (o := VG.Impl.Rsa.X86_64.Crt.aT)
    (sl := sCtr) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (c := l.dbls) hdb.1
    hdb.2 cx₂ (by rw [me₂, hv₁, hN₁]; exact hY)) fun t ⟨hv, hf, hH, k⟩ => ⟨?_, ?_, hH, ?_⟩
  · rw [hv, me₂, hN₁, hv₁]
  · exact (Frm.of_outside (ho₁.mono (o' := slot wx VG.Impl.Rsa.X86_64.Crt.aT) (n' := 8 * (wx + 2))
      (Nat.le_refl _) (by omega_using [])) (by simp [k1Ranges])).trans (by rw [← me₂]; exact hf)
  · exact ((k₁.trans k₂).trans k).mono (by decide)

/-! ## Facts about the area that the region's steps carry -/

/-- The twenty limbs of `v` at offset `e` of the area `F`. -/
def Limbs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (F : Addr) (e v : Nat) : Prop :=
  ∀ k < l.L, word m F (e + l.off k) = BitVec.ofNat 64 (limbN v k)

theorem Limbs.of_frm (hl : LayOk l) {m m' : Mem} {B : Addr} {a e v : Nat} {rs : List (Nat × Nat)} (h : Limbs l m (off B a) e v)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, a + e + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ a + e) (hz : a + e + l.NB ≤ 2 ^ 64) :
    Limbs l m' (off B a) e v := fun k hk => by
  have := off_lt hl hk
  rw [word_off, hf.word_eq (fun r hr => by rcases hd r hr with h | h <;> omega_using [this, h]) (by omega_using [hz, this]), ← word_off]
  exact h k hk

/-- `arr52` in a prime's workspace (`rdi = off B o`, 16 words), the area at `off B a`. -/
theorem arr52r_ok (hl : LayOk l) {t : State} {B : Addr} {Z o a p j c : Nat} {mx : BitVec 64} (hs : Scr t B Z)
    (hdi : t.gpr .rdi = off B o) (hH : Hdr t.mem (off B o) l.W mx)
    (hia : word t.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a)
    (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2) (hc : c + l.NB ≤ l.D) (hj : j < 8) :
    WP isa (.block (arr52 l p j c)) t fun t' =>
      Limbs l t'.mem (off B a) (l.D * p + c) (wv t.mem (off B o) (slot l.W j) l.W) ∧
      Frm B [(a + (l.D * p + c), l.NB)] t.mem t'.mem ∧
      Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] t t' ∧ t'.gpr .r12 = mask52 ∧ t'.mxcsr = t.mxcsr := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have lj := slot_le (w := l.W) hj
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hH' : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [hoa, haZ, this])
  refine WP.mono (arr52_ok hl (A := off B a) (Aj := off (off B o) (slot l.W j)) hdi hH'
    (by unfold sArr; omega_arith) (hH.harr j hj) hia (by omega_using [hc, hDb2, hDp])
    (fun i hi => by rw [off_off, AmmSym.off_add]; exact hs.ld (by omega_using [hoa, haZ, lj, hi]))
    (fun k hk => by
      have := off_lt hl hk
      rw [off_off, AmmSym.off_add]; exact hs.st (by omega_using [haZ, hc, hDp, this]))
    (fun m m' ho i hi => by
      rw [off_off] at ho
      rw [off_off, word_off, word_off]
      exact (Frm.of_outside_off ho (by omega_using [haZ, hc, hn, hDp]) (by omega_using [haZ, hc, hn, hDp])).word_eq
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_using [hoa, lj, hi]))
            (by omega_using [hoa, haZ, hn, lj, hi])))
    fun t' ⟨hv, ho, k, h12, hx⟩ => ⟨fun k hk => ?_, ?_, k, h12, hx⟩
  · rw [← word_off, hv k hk, wv_off, Nat.add_zero]
  · rw [off_off] at ho
    have := Frm.of_outside_off ho (by omega_using [haZ, hc, hn, hDp]) (by omega_using [haZ, hc, hn, hDp])
    simpa only [Nat.add_zero] using this

/-- `arr52` after earlier changes within region `p`, from `s₁`. -/
theorem arrA_ok (hl : LayOk l) {s₁ t : State} {B : Addr} {Z o a p j c : Nat} {mx : BitVec 64} (hs : Scr s₁ B Z)
    (hdi : s₁.gpr .rdi = off B o) (hH : Hdr s₁.mem (off B o) l.W mx)
    (hia : word s₁.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a)
    (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2) (hc : c + l.NB ≤ l.D) (hj : j < 8)
    (hf : Frm B [(a + l.D * p, l.D)] s₁.mem t.mem) (hwr : t.wr = s₁.wr) (hdt : t.gpr .rdi = s₁.gpr .rdi) :
    WP isa (.block (arr52 l p j c)) t fun t' =>
      Limbs l t'.mem (off B a) (l.D * p + c) (wv s₁.mem (off B o) (slot l.W j) l.W) ∧
      Frm B [(a + l.D * p, l.D)] s₁.mem t'.mem ∧ Frm B [(a + (l.D * p + c), l.NB)] t.mem t'.mem ∧
      t'.wr = s₁.wr ∧ t'.gpr .rdi = s₁.gpr .rdi ∧
      Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] t t' ∧ t'.gpr .r12 = mask52 := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have lj := slot_le (w := l.W) hj
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hr : ∀ r ∈ [(a + l.D * p, l.D)], a ≤ r.1 := fun r h => by rw [List.mem_singleton.mp h]; simp only; omega_using []
  have hia' : word t.mem (off B o) (8 * sIfma) = off B a := by
    rw [word_off, word_below_frm hf hr (by unfold sIfma sFn; omega_using [hoa, hT]) (by omega_using [haZ, hn]), ← word_off]; exact hia
  have hwv : wv t.mem (off B o) (slot l.W j) l.W = wv s₁.mem (off B o) (slot l.W j) l.W := by
    rw [wv_off, wv_off, wv_below_frm hf hr (by omega_using [hoa, lj]) (by omega_using [haZ, hn])]
  refine WP.mono (arr52r_ok hl (hs.congr hwr) (hdt.trans hdi)
    (hH.of_below hf (fun r h => by have := hr r h; unfold hdrBytes; unfold slot hdrBytes at h8; omega_using [hoa, hT, this])
      (by unfold hdrBytes; omega_using [hoa, haZ, hn, hT])) hia' hoa haZ hp hc hj)
    fun t' ⟨hv, f', k, h12, _⟩ => ⟨by rw [hwv] at hv; exact hv, ?_, f', ?_, ?_, k, h12⟩
  · exact hf.trans (f'.widen fun r h => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp h]; simp only; omega_using [hc]⟩)
  · rw [k.2.2, hwr]
  · rw [k.gpr (by decide), hdt]

/-- `k1`'s ranges miss an array of the prime but `aAcc`, `aTmp`, `aT`. -/
theorem k1Ranges_arr {j : Nat} (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ aT) :
    ∀ r ∈ k1Ranges l.W, slot l.W j + 8 * l.W ≤ r.1 ∨ r.1 + r.2 ≤ slot l.W j := by
  have := slot_sep (w := l.W) h1
  have := slot_sep (w := l.W) h2
  have := slot_sep (w := l.W) h3
  have := hdr_lt_slot l.W j (show sCtr < 32 by decide)
  simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCtr, sFn] at * <;> omega_arith

/-- `region`'s start: `2¹⁰⁵⁶ mod X` into `aT`, then the modulus, it, `x R`
and `R` into region `p`. -/
theorem regionA_ok (hl : LayOk l) {s : State} {B : Addr} {Z o w a p X : Nat} {mx : BitVec 64} (hc : SubCtx s B Z o w l.W mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a)
    (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2) (hN : wv s.mem (off B o) (slot l.W Public.aN) l.W = X)
    (hY : wv s.mem (off B o) (slot l.W Public.aY) l.W < X) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (k1 l ++ ([.block (arr52 l p Public.aN oM),
      .block (arr52 l p aT l.oK1), .block (arr52 l p aXc l.oX),
      .block (arr52 l p Public.aY l.oY)] : List (Prog isa)))) s fun t =>
      Limbs l t.mem (off B a) (l.D * p + oM) X ∧
      Limbs l t.mem (off B a) (l.D * p + l.oK1) (2 ^ l.dbls * wv s.mem (off B o) (slot l.W Public.aY) l.W % X) ∧
      Limbs l t.mem (off B a) (l.D * p + l.oX) (wv s.mem (off B o) (slot l.W aXc) l.W) ∧
      Limbs l t.mem (off B a) (l.D * p + l.oY) (wv s.mem (off B o) (slot l.W Public.aY) l.W) ∧
      Frm B (shiftRanges o (k1Ranges l.W) ++ [(a + l.D * p, l.D)]) s.mem t.mem ∧
      t.wr = s.wr ∧ t.gpr .rdi = off B o ∧ Keep mmRegs s t ∧ t.gpr .r12 = mask52 ∧
      Hdr t.mem (off B o) l.W mx ∧ word t.mem (off B o) (8 * sIfma) = off B a := by
  have hs := hc.scr
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hk1 : ∀ r ∈ k1Ranges l.W, r.1 + r.2 ≤ slot l.W 8 := by
    have := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
    have := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
    have := slot_le (w := l.W) (show aT < 8 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCtr, sFn] <;> omega_arith
  refine wp_seqs_append (by simp [k1, copyArr]) (by simp) (WP.mono (k1_ok hl hc.good (by have := W_bounds hl; omega_using [this])
    (by have := W_bounds hl; omega_using [this]) hN hY) fun s₁ ⟨hT₁, f₁, hH₁, k₁⟩ => ?_)
  have hs₁ : Scr s₁ B Z := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = off B o := by rw [k₁.gpr (by decide)]; exact hc.rdi
  have hwv : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv s₁.mem (off B o) (slot l.W j) l.W = wv s.mem (off B o) (slot l.W j) l.W := fun j hj h1 h2 h3 => by
    have := slot_le (w := l.W) hj
    exact f₁.wv_eq (k1Ranges_arr h1 h2 h3) (by omega_using [hoa, haZ, hn, this])
  have hia₁ : word s₁.mem (off B o) (8 * sIfma) = off B a := by
    rw [f₁.word_eq (fun r hr => by
      have := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
      have := hdr_lt_slot l.W Public.aAcc (show sIfma < 32 by decide)
      have := hdr_lt_slot l.W Public.aTmp (show sIfma < 32 by decide)
      have := hdr_lt_slot l.W aT (show sIfma < 32 by decide)
      simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [sCtr, sIfma, sFn] at * <;> omega_arith)
      (by unfold sIfma sFn; omega_using [])]
    exact hia
  have f₁' : Frm B (shiftRanges o (k1Ranges l.W)) s.mem s₁.mem :=
    f₁.rebase (by omega_using [hoa, haZ, hn]) fun r hr => by have := hk1 r hr; omega_using [hoa, haZ, hn, this]
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (arrA_ok hl hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := Public.aN) (c := oM) (by omega_using [hDb1, hoM])
    (by decide) (Frm.refl _ _ _) rfl rfl) fun t₁ ⟨lM, g₁, _, w₁, d₁, k₁', _⟩ => ?_)
  refine WP.seq (WP.mono (arrA_ok hl hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := aT) (c := l.oK1) (by omega_using [o7, o10]) (by decide)
    g₁ w₁ d₁) fun t₂ ⟨lK, g₂, e₂, w₂, d₂, k₂, _⟩ => ?_)
  refine WP.seq (WP.mono (arrA_ok hl hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := aXc) (c := l.oX) (by omega_using [o3, o10]) (by decide)
    g₂ w₂ d₂) fun t₃ ⟨lX, g₃, e₃, w₃, d₃, k₃, _⟩ => ?_)
  refine WP.mono (arrA_ok hl hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := Public.aY) (c := l.oY) (by omega_using [o2, o10]) (by decide)
    g₃ w₃ d₃) fun t ⟨lY, g₄, e₄, w₄, d₄, k₄, h12⟩ => ?_
  have sep : ∀ {c c' : Nat}, c + l.NB ≤ c' ∨ c' + l.NB ≤ c → ∀ r ∈ [(a + (l.D * p + c'), l.NB)],
      a + (l.D * p + c) + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ a + (l.D * p + c) := fun h r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [h]
  rw [(hwv _ (by decide) (by decide) (by decide) (by decide)).trans hN] at lM
  rw [hT₁] at lK
  rw [hwv _ (by decide) (by decide) (by decide) (by decide)] at lX lY
  refine ⟨((lM.of_frm hl e₂ (sep (by omega_using [o7, hoM])) (by omega_using [haZ, hn, hDb1, hoM, hDp])).of_frm hl e₃
      (sep (by omega_using [o3, hoM])) (by omega_using [haZ, hn, hDb1, hoM, hDp])).of_frm hl e₄
      (sep (by omega_using [o2, hoM])) (by omega_using [haZ, hn, hDb1, hoM, hDp]),
          (lK.of_frm hl e₃ (sep (by omega_using [o3, o7])) (by omega_using [haZ, hn, o7, o10, hDp])).of_frm hl e₄ (sep
          (by omega_using [o2, o7]))
      (by omega_using [haZ, hn, o7, o10, hDp]),
          lX.of_frm hl e₄ (sep (by omega_using [o2, o3])) (by omega_using [haZ, hn, o3, o10, hDp]), lY, f₁'.append g₄,
    w₄.trans k₁.2.2, d₄.trans hdi₁, ?_, h12, ?_, ?_⟩
  · exact (k₁.trans (((k₁'.trans k₂).trans k₃).trans k₄)).mono (by decide)
  · exact hH₁.of_below g₄ (fun r hr => by
      rw [List.mem_singleton.mp hr]; unfold hdrBytes; unfold slot hdrBytes at h8; simp only; omega_using [hoa, hT])
      (by unfold hdrBytes; unfold slot hdrBytes at h8; omega_using [hoa, haZ, hn, hT])
  · rw [word_off, word_below_frm g₄ (L := a) (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [])
      (by unfold sIfma sFn; omega_using [hoa, hT]) (by omega_using [haZ, hn]), ← word_off]
    exact hia₁

/-! ## The region's tail -/

/-- `k0St` in a prime's workspace, the area at `off B a`. -/
theorem k0r_ok (hl : LayOk l) {u : State} {B : Addr} {Z o a p : Nat} {mx : BitVec 64} (hs : Scr u B Z)
    (hdi : u.gpr .rdi = off B o) (hH : Hdr u.mem (off B o) l.W mx)
    (hia : word u.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a)
    (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2) (h12 : u.gpr .r12 = mask52) :
    WP isa (.block (k0St l p)) u fun u' =>
      (∀ t < 4, word u'.mem (off B a) (l.D * p + l.oK0 + 8 * t) = mx &&& mask52) ∧
      Frm B [(a + l.D * p + l.oK0, 32)] u.mem u'.mem ∧ u'.gpr .r11 = off (off B a) (l.D * p) ∧
      Keep [.rax, .r11] u u' := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hH' : ∀ i < 32, InRegions (u.rd ++ u.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [hoa, haZ, this])
  refine WP.mono (k0St_ok (A := off B a) hdi hH' hia hH.hminv h12 (by omega_using [hDb2, hDp]) (by omega_using [o1, hDb2]) fun t ht => by
    rw [off_off, AmmSym.off_add]; exact hs.st (by omega_using [haZ, o1, o10, hDp, ht])) fun u' ⟨hw, ho, r11,
        k, _⟩ => ⟨fun t ht => ?_, ?_, r11, k⟩
  · rw [Nat.add_assoc, ← word_off]; exact hw t ht
  · rw [off_off] at ho
    exact Frm.of_outside_off ho (by omega_using [haZ, hn, hDp]) (by omega_using [haZ, hn, o1, o10, hDp])

/-- `eZero` with `r11` at region `p` of the area `off B a`. -/
theorem eZr_ok (hl : LayOk l) {u : State} {B : Addr} {Z a p : Nat} (hs : Scr u B Z) (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2)
    (h11 : u.gpr .r11 = off (off B a) (l.D * p)) :
    WP isa (.block (eZero l)) u fun u' =>
      (∀ i < l.E, u'.mem (off (off B a) (l.D * p + l.oE + i)) = 0) ∧
      Frm B [(a + l.D * p + l.oE, l.E)] u.mem u'.mem ∧ u'.gpr .rax = 0 ∧ Keep [.rax] u u' := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have hEW : l.E = 8 * l.W := rfl
  refine WP.mono (eZero_ok h11 (by omega_using [o6, o10, hDb2]) fun i hi => by
    rw [off_off, AmmSym.off_add]; exact hs.st (by omega_using [haZ, o6, o10, hDp, hEW, hi])) fun u' ⟨hw, ho, ra,
        k, _⟩ => ⟨fun i hi => ?_, ?_, ra, k⟩
  · have e := byte_of_word0 (hw (i / 8) (by omega_using [hEW, hi])) (show i % 8 < 8 from Nat.mod_lt _ (by decide))
    rw [show l.D * p + l.oE + i = l.D * p + (l.oE + 8 * (i / 8) + i % 8) by omega_using [], ← off_off]
    exact e
  · rw [off_off] at ho
    exact Frm.of_outside_off ho (by omega_using [haZ, hn, hDp]) (by omega_using [haZ, hn, o6, o10, hDp])

/-- `finOne` with `r11` at `q`'s region (`rax = 0`). -/
theorem finr_ok (hl : LayOk l) {u : State} {B : Addr} {Z a : Nat} (hs : Scr u B Z) (haZ : a + 2 * l.D + 8 ≤ Z)
    (h11 : u.gpr .r11 = off (off B a) (l.D * 1)) (ha : u.gpr .rax = 0) :
    WP isa (.block (finOne l)) u fun u' =>
      Limbs l u'.mem (off B a) (l.D * 1 + l.oFin) 1 ∧ Frm B [(a + l.D * 1 + l.oFin, l.NB)] u.mem u'.mem ∧
      Keep [.rax] u u' := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  refine WP.mono (finOne_ok hl h11 ha (by omega_using [o9, o10, hDb2]) fun j hj => by
    have := off_lt hl hj
    rw [off_off, AmmSym.off_add]; exact hs.st (by omega_using [haZ, o9, o10, this])) fun u' ⟨hw, ho, k, _⟩ => ⟨fun j hj => ?_, ?_, k⟩
  · rw [Nat.add_assoc, ← word_off]; exact hw j hj
  · rw [off_off] at ho
    exact Frm.of_outside_off ho (by omega_using [haZ, hn]) (by omega_using [haZ, hn, o9, o10])

/-- `eCopy` with `r11` at region `p` of the area `off B a`: the exponent's
bytes (`eb`, its pointer and length in `n`'s slots `sp` and `sl`) at the end
of the l.E at `l.oE`. -/
theorem eCr_ok (hl : LayOk l) {u : State} {B : Addr} {Z o a p sp sl L : Nat} {ep : Addr} {eb : List Byte} (hs : Scr u B Z)
    (hdi : u.gpr .rdi = off B o) (hlk : word u.mem (off B o) (8 * sLink) = B)
    (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2)
    (hsp : sp < 32) (hsl : sl < 32) (hpv : word u.mem B (8 * sp) = ep)
    (hlv : word u.mem B (8 * sl) = BitVec.ofNat 64 L) (he : Src u B Z ep eb) (hL : eb.length = L)
    (hL1 : 1 ≤ L) (hL2 : L ≤ l.E) (h11 : u.gpr .r11 = off (off B a) (l.D * p)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (eCopy l sp sl)) u fun u' =>
      (∀ i (h : i < L), u'.mem (off (off B a) (l.D * p + l.oE + (l.E - L + i))) = eb[i]'(by omega_using [hL, h])) ∧
      Frm B [(a + l.D * p + l.oE + (l.E - L), L)] u.mem u'.mem ∧ Keep [.rax, .rcx, .rsi, .r11] u u' := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hC : ∀ i, off (off (off B a) (l.D * p)) (l.oE + l.E - L) + BitVec.ofNat 64 i =
      off B (a + l.D * p + l.oE + (l.E - L) + i) := fun i => by
    rw [AmmSym.off_add, off_off, off_off]; congr 1; omega_using [hL2]
  refine WP.mono (eCopy_ok (B := B) (W := off B o) hL hL1 hL2 (by omega_using [o6, o10, hDb2]) hdi h11
    (by rw [off_off]; exact hs.ld (by unfold sLink sFn; omega_using [hoa, haZ, hT])) hlk
    (hs.ld (by unfold slot hdrBytes at h8; omega_using [hoa, haZ, hsp, hT])) (hs.ld
        (by unfold slot hdrBytes at h8; omega_using [hoa, haZ, hsl, hT])) hpv hlv
    (fun i hi => he.rd i (by omega_using [hL, hi])) (fun i hi => he.val i (by omega_using [hL, hi]))
    (fun i hi => by rw [hC]; exact hs.st8 (by omega_using [haZ, hL2, o6, o10, hDp, hi]))
    (fun m m' ho i hi => by
      rw [off_off, off_off] at ho
      exact Frm.of_outside_off ho (by omega_using [haZ, hn, o6, o10, hDp]) (by omega_using [haZ, hL2, hn, o6, o10, hDp]) _ fun r hr => by
        rw [List.mem_singleton.mp hr]; have := he.out i (by omega_using [hL, hi]); simp only; omega_using [haZ, hL2, o6, o10, hDp, this]))
    fun u' ⟨hb, ho, k, _⟩ => ⟨fun i hi => ?_, ?_, k⟩
  · have e := hb i hi
    rw [hC] at e
    rw [off_off]
    rw [show a + (l.D * p + l.oE + (l.E - L + i)) = a + l.D * p + l.oE + (l.E - L) + i by omega_using []]
    exact e
  · rw [off_off, off_off] at ho
    have := Frm.of_outside_off ho (by omega_using [haZ, hn, o6, o10, hDp]) (by omega_using [haZ, hL2, hn, o6, o10, hDp])
    rwa [show a + (l.D * p + (l.oE + l.E - L)) + 0 = a + l.D * p + l.oE + (l.E - L) by omega_using [hL2]] at this

/-! ## The exponent's value -/

/-- The exponent padded with zero bytes at the top to l.E. -/
def padE (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (eb : List Byte) : List Byte := List.replicate (l.E - eb.length) 0 ++ eb

/-- The bytes at `l.oE` read as `ev` reads them: big-endian. -/
theorem ev_os2ip (m : Mem) (F : Addr) (p : Nat) (bs : List Byte)
    (h : ∀ i (hi : i < bs.length), m (off F (l.D * p + l.oE + i)) = bs[i]) :
    ∀ n ≤ bs.length, ev l m F p n = Spec.Rsa.os2ip (bs.take n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [ev, ev_os2ip m F p bs h n (by omega_using [hn]), List.take_add_one, List.getElem?_eq_getElem (by omega_using [hn]),
      Option.toList_some, os2ip_snoc, h n (by omega_using [hn]), Nat.mul_comm]

theorem ev_padE {m : Mem} {F : Addr} {p : Nat} {eb : List Byte} (hL : eb.length ≤ l.E)
    (h : ∀ i, i < l.E → m (off F (l.D * p + l.oE + i)) = (padE l eb).getD i 0) :
    ev l m F p l.E = Spec.Rsa.os2ip eb := by
  have hl : (padE l eb).length = l.E := by simp only [padE, List.length_append, List.length_replicate]; omega_using [hL]
  have := ev_os2ip m F p (padE l eb) (fun i hi => by
    rw [h i (by omega_arith), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_using [hi]), Option.getD_some]) l.E
    (by omega_using [hl])
  rw [this, show (padE l eb).take l.E = padE l eb by rw [List.take_of_length_le (by omega_using [hl])], padE, os2ip_zeros]

/-! ## The tail of a region -/

/-- What the tail's steps read: the prime's workspace `off B o` (16 words),
the area's base in it, `n`'s slots `sp` and `sl` (the exponent's pointer and
length), and the exponent. -/
structure TCtx (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (u : State) (B : Addr) (Z o a : Nat) (mx : BitVec 64) (sp sl : Nat) (ep : Addr)
    (eb : List Byte) : Prop where
  scr : Scr u B Z
  rdi : u.gpr .rdi = off B o
  hdr : Hdr u.mem (off B o) l.W mx
  ia : word u.mem (off B o) (8 * sIfma) = off B a
  lk : word u.mem (off B o) (8 * sLink) = B
  pv : word u.mem B (8 * sp) = ep
  lv : word u.mem B (8 * sl) = BitVec.ofNat 64 eb.length
  src : Src u B Z ep eb

theorem TCtx.of_frm {u u' : State} {B : Addr} {Z o a : Nat} {mx : BitVec 64} {sp sl : Nat} {ep : Addr}
    {eb : List Byte} (h : TCtx l u B Z o a mx sp sl ep eb) {rs : List (Nat × Nat)} (hf : Frm B rs u.mem u'.mem)
    (hr : ∀ r ∈ rs, a ≤ r.1 ∧ r.1 + r.2 ≤ Z) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a ≤ Z) (hsp : sp < 32)
    (hsl : sl < 32) (k : Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] u u') : TCtx l u' B Z o a mx sp sl ep eb := by
  have hn := h.scr.nowrap
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hr' : ∀ r ∈ rs, a ≤ r.1 := fun r hr' => (hr r hr').1
  have hw : ∀ d, d + 8 ≤ a → word u'.mem B d = word u.mem B d := fun d hd =>
    word_below_frm hf hr' hd (by unfold slot hdrBytes at h8; omega_using [haZ, hn])
  refine ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi,
    h.hdr.of_below hf (fun r hr'' => by have := hr' r hr''; unfold hdrBytes; unfold slot hdrBytes at h8; omega_using [hoa, hT, this])
      (by unfold hdrBytes; unfold slot hdrBytes at h8; omega_using [hoa, haZ, hn, hT]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [word_off, hw _ (by unfold sIfma sFn; omega_using [hoa, hT]), ← word_off]; exact h.ia
  · rw [word_off, hw _ (by unfold sLink sFn; omega_using [hoa, hT]), ← word_off]; exact h.lk
  · rw [hw _ (by unfold slot hdrBytes at h8; omega_using [hoa, hsp, hT])]; exact h.pv
  · rw [hw _ (by unfold slot hdrBytes at h8; omega_using [hoa, hsl, hT])]; exact h.lv
  · exact h.src.congr (InScr.of_frm hf fun r hr'' => (hr r hr'').2) k.2.1 k.2.2

theorem padE_lo {eb : List Byte} {i : Nat} (hi : i < l.E - eb.length) : (padE l eb).getD i 0 = 0 := by
  rw [padE, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_replicate]; omega_using [hi]),
    List.getElem?_replicate]
  simp only [hi, ↓reduceIte, Option.getD_some]

theorem padE_hi {eb : List Byte} {i : Nat} (h1 : l.E - eb.length ≤ i) (h2 : i < l.E) (_hL : eb.length ≤ l.E) :
    (padE l eb).getD i 0 = eb[i - (l.E - eb.length)]'(by omega_using [h1, h2]) := by
  rw [padE, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_replicate]; omega_using [h1]),
    List.length_replicate, List.getElem?_eq_getElem (by omega_using [h1, h2]), Option.getD_some]

/-- The ranges a region's tail writes. -/
def tailR (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (a p : Nat) : List (Nat × Nat) :=
  [(a + l.D * p + l.oFin, l.NB), (a + l.D * p + l.oK0, 32), (a + l.D * p + l.oE, l.E)]

theorem tailR_bound (hl : LayOk l) {a p Z : Nat} (hp : p < 2) (haZ : a + 2 * l.D + 8 ≤ Z) :
    ∀ r ∈ tailR l a p, a ≤ r.1 ∧ r.1 + r.2 ≤ Z := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  simp only [tailR, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> constructor <;> simp only <;> omega_using [haZ, o9, o10, hDp, o1, o6]

/-- `p`'s tail: `R mod p` as the last multiplier, `k₀`, and the exponent. -/
theorem regionB0_ok (hl : LayOk l) {u : State} {B : Addr} {Z o a sp sl : Nat} {mx : BitVec 64} {ep : Addr} {eb : List Byte}
    (hc : TCtx l u B Z o a mx sp sl ep eb) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z)
    (hsp : sp < 32) (hsl : sl < 32) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ l.E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (([.block (arr52 l 0 Public.aY l.oFin), .block (k0St l 0),
      .block (eZero l)] : List (Prog isa)) ++ eCopy l sp sl)) u fun u' =>
      Limbs l u'.mem (off B a) (l.D * 0 + l.oFin) (wv u.mem (off B o) (slot l.W Public.aY) l.W) ∧
      (∀ t < 4, word u'.mem (off B a) (l.D * 0 + l.oK0 + 8 * t) = mx &&& mask52) ∧
      (∀ i, i < l.E → u'.mem (off (off B a) (l.D * 0 + l.oE + i)) = (padE l eb).getD i 0) ∧
      Frm B (tailR l a 0) u.mem u'.mem ∧ Keep mmRegs u u' := by
  have hn := hc.scr.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hB := tailR_bound hl (a := a) (p := 0) (by decide) haZ
  refine wp_seqs_append (by simp) (by simp [eCopy]) ?_
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (arr52r_ok hl hc.scr hc.rdi hc.hdr hc.ia hoa haZ (p := 0) (c := l.oFin) (j := Public.aY)
    (by decide) (by omega_using [o9, o10]) (by decide)) fun u₁ ⟨lF, f₁, k₁, r12₁, _⟩ => ?_)
  have c₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [haZ, o9, o10]) hoa (by omega_using [haZ])
    hsp hsl k₁
  refine WP.seq (WP.mono (k0r_ok hl c₁.scr c₁.rdi c₁.hdr c₁.ia hoa haZ (p := 0) (by decide) r12₁)
    fun u₂ ⟨hk, f₂, r11₂, k₂⟩ => ?_)
  have c₂ := c₁.of_frm f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [haZ, o1, o10]) hoa (by omega_using [haZ])
    hsp hsl (k₂.mono (by decide))
  refine WP.mono (eZr_ok hl c₂.scr haZ (p := 0) (by decide) r11₂) fun u₃ ⟨hz, f₃, _, k₃⟩ => ?_
  have c₃ := c₂.of_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [haZ, o6, o10]) hoa (by omega_using [haZ])
    hsp hsl (k₃.mono (by decide))
  have r11₃ : u₃.gpr .r11 = off (off B a) (l.D * 0) := by rw [k₃.gpr (by decide)]; exact r11₂
  refine WP.mono (eCr_ok hl c₃.scr c₃.rdi c₃.lk hoa haZ (p := 0) (by decide) hsp hsl c₃.pv c₃.lv c₃.src rfl hL1 hL2
    r11₃) fun u' ⟨hb, f₄, k₄⟩ => ?_
  refine ⟨((lF.of_frm hl f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o1, o9])
      (by omega_using [haZ, hn, o9, o10])).of_frm hl f₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o6, o9]) (by omega_using [haZ, hn, o9, o10])).of_frm hl f₄
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [hL2, o6, o9])
          (by omega_using [haZ, hn, o9, o10]), fun t ht => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · rw [word_off, f₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o1, o6, ht])
      (by omega_using [haZ, hn, o1, o10, ht]),
      f₃.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o1, o6, ht])
          (by omega_using [haZ, hn, o1, o10, ht]), ← word_off]
    exact hk t ht
  · by_cases hlo : i < l.E - eb.length
    · rw [padE_lo hlo, off_off, byte_frm f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [hlo])
        (by omega_using [haZ, hn, o6, o10, hlo]), ← off_off]
      exact hz i hi
    · rw [padE_hi (by omega_using [hlo]) hi hL2, show l.D * 0 + l.oE + i = l.D * 0 + l.oE + (l.E - eb.length + (i - (l.E - eb.length)))
        by omega_using [hlo]]
      exact hb _ (by omega_using [hi, hlo])
  · refine (((f₁.append f₂).append f₃).append f₄).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((rfl | rfl) | rfl) | rfl
    · exact ⟨_, List.mem_cons_self .., by simp only; omega_using []⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_using []⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega_using []⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega_using [hL2]⟩
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)

/-- `q`'s tail: `k₀`, 1 as the last multiplier, and the exponent. -/
theorem regionB1_ok (hl : LayOk l) {u : State} {B : Addr} {Z o a sp sl : Nat} {mx : BitVec 64} {ep : Addr} {eb : List Byte}
    (hc : TCtx l u B Z o a mx sp sl ep eb) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z)
    (hsp : sp < 32) (hsl : sl < 32) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ l.E) (h12 : u.gpr .r12 = mask52) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (([.block (k0St l 1), .block (eZero l), .block (finOne l)] :
      List (Prog isa)) ++ eCopy l sp sl)) u fun u' =>
      Limbs l u'.mem (off B a) (l.D * 1 + l.oFin) 1 ∧
      (∀ t < 4, word u'.mem (off B a) (l.D * 1 + l.oK0 + 8 * t) = mx &&& mask52) ∧
      (∀ i, i < l.E → u'.mem (off (off B a) (l.D * 1 + l.oE + i)) = (padE l eb).getD i 0) ∧
      Frm B (tailR l a 1) u.mem u'.mem ∧ Keep mmRegs u u' := by
  have hn := hc.scr.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  refine wp_seqs_append (by simp) (by simp [eCopy]) ?_
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (k0r_ok hl hc.scr hc.rdi hc.hdr hc.ia hoa haZ (p := 1) (by decide) h12)
    fun u₁ ⟨hk, f₁, r11₁, k₁⟩ => ?_)
  have c₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [haZ, o1, o10]) hoa (by omega_using [haZ])
    hsp hsl (k₁.mono (by decide))
  refine WP.seq (WP.mono (eZr_ok hl c₁.scr haZ (p := 1) (by decide) r11₁) fun u₂ ⟨hz, f₂, ra₂, k₂⟩ => ?_)
  have c₂ := c₁.of_frm f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [haZ, o6, o10]) hoa (by omega_using [haZ])
    hsp hsl (k₂.mono (by decide))
  have r11₂ : u₂.gpr .r11 = off (off B a) (l.D * 1) := by rw [k₂.gpr (by decide)]; exact r11₁
  refine WP.mono (finr_ok hl c₂.scr haZ r11₂ ra₂) fun u₃ ⟨lF, f₃, k₃⟩ => ?_
  have c₃ := c₂.of_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [haZ, o9, o10]) hoa (by omega_using [haZ])
    hsp hsl (k₃.mono (by decide))
  have r11₃ : u₃.gpr .r11 = off (off B a) (l.D * 1) := by rw [k₃.gpr (by decide)]; exact r11₂
  refine WP.mono (eCr_ok hl c₃.scr c₃.rdi c₃.lk hoa haZ (p := 1) (by decide) hsp hsl c₃.pv c₃.lv c₃.src rfl hL1 hL2
    r11₃) fun u' ⟨hb, f₄, k₄⟩ => ?_
  refine ⟨lF.of_frm hl f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [hL2, o6, o9])
      (by omega_using [haZ, hn, o9, o10]), fun t ht => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · rw [word_off, f₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o1, o6, ht])
      (by omega_using [haZ, hn, o1, o10, ht]),
      f₃.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o1, o9, ht])
          (by omega_using [haZ, hn, o1, o10, ht]),
      f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o1, o6, ht])
          (by omega_using [haZ, hn, o1, o10, ht]), ← word_off]
    exact hk t ht
  · by_cases hlo : i < l.E - eb.length
    · rw [padE_lo hlo, off_off, byte_frm f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [hlo])
        (by omega_using [haZ, hn, o6, o10, hlo]),
            byte_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [o6, o9, hlo])
        (by omega_using [haZ, hn, o6, o10, hlo]), ← off_off]
      exact hz i hi
    · rw [padE_hi (by omega_using [hlo]) hi hL2, show l.D * 1 + l.oE + i = l.D * 1 + l.oE + (l.E - eb.length + (i - (l.E - eb.length)))
        by omega_using [hlo]]
      exact hb _ (by omega_using [hi, hlo])
  · refine (((f₁.append f₂).append f₃).append f₄).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((rfl | rfl) | rfl) | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_using []⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega_using []⟩
    · exact ⟨_, List.mem_cons_self .., by simp only; omega_using []⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega_using [hL2]⟩
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)

/-! ## A region -/

/-- Region `p` of the area `F`: the modulus, `2¹⁰⁵⁶ mod X`, the base, `R`,
the last multiplier, `k₀`, and the padded exponent. -/
structure RegOut (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (F : Addr) (p X K1 Xc Y Fin : Nat) (k0 : BitVec 64) (eb : List Byte) : Prop where
  n : Limbs l m F (l.D * p + oM) X
  k1 : Limbs l m F (l.D * p + l.oK1) K1
  x : Limbs l m F (l.D * p + l.oX) Xc
  y : Limbs l m F (l.D * p + l.oY) Y
  fin : Limbs l m F (l.D * p + l.oFin) Fin
  k0 : ∀ t < 4, word m F (l.D * p + l.oK0 + 8 * t) = k0
  e : ∀ i, i < l.E → m (off F (l.D * p + l.oE + i)) = (padE l eb).getD i 0

/-- A region after changes outside it. -/
theorem RegOut.of_frm (hl : LayOk l) {m m' : Mem} {B : Addr} {a p X K1 Xc Y Fin : Nat} {k0 : BitVec 64} {eb : List Byte}
    (h : RegOut l m (off B a) p X K1 Xc Y Fin k0 eb) {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hd : ∀ r ∈ rs, a + l.D * p + l.D ≤ r.1 ∨ r.1 + r.2 ≤ a + l.D * p) (hz : a + l.D * p + l.D ≤ 2 ^ 64) :
    RegOut l m' (off B a) p X K1 Xc Y Fin k0 eb := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hlr : ∀ {c}, c + l.NB ≤ l.D → ∀ r ∈ rs, a + (l.D * p + c) + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ a + (l.D * p + c) :=
    fun hc r hr => by rcases hd r hr with h | h <;> omega_using [hc, h]
  exact ⟨h.n.of_frm hl hf (hlr (by omega_using [hDb1, hoM])) (by omega_using [hz, hDb1, hoM]),
    h.k1.of_frm hl hf (hlr (by omega_using [o7, o10])) (by omega_using [hz, o7, o10]),
    h.x.of_frm hl hf (hlr (by omega_using [o3, o10])) (by omega_using [hz, o3, o10]),
        h.y.of_frm hl hf (hlr (by omega_using [o2, o10])) (by omega_using [hz, o2, o10]),
    h.fin.of_frm hl hf (hlr (by omega_using [o9, o10])) (by omega_using [hz, o9, o10]),
    fun t ht => by
      rw [word_off, hf.word_eq (fun r hr => by rcases hd r hr with h | h <;> omega_using [o1, o10, ht, h])
          (by omega_using [hz, o1, o10, ht]), ← word_off]
      exact h.k0 t ht,
    fun i hi => by
      rw [off_off, byte_frm hf (fun r hr => by rcases hd r hr with h | h <;> omega_using [o6, o10, hi, h])
          (by omega_using [hz, o6, o10, hi]), ← off_off]
      exact h.e i hi⟩

/-- The prime's workspace and `n`'s slots after `regionA`, for the tail. -/
theorem TCtx.of_regionA (hl : LayOk l) {s t : State} {B : Addr} {Z o w a p sp sl : Nat} {mx : BitVec 64} {ep : Addr}
    {eb : List Byte} (hc : SubCtx s B Z o w l.W mx) (hoa : o + slot l.W 8 + tabBytes l.W ≤ a)
    (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2) (hsp : sp < 32) (hsl : sl < 32)
    (hpv : word s.mem B (8 * sp) = ep) (hlv : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (he : Src s B Z ep eb) (hf : Frm B (shiftRanges o (k1Ranges l.W) ++ [(a + l.D * p, l.D)]) s.mem t.mem)
    (hwr : t.wr = s.wr) (hrd : t.rd = s.rd) (hdi : t.gpr .rdi = off B o) (hH : Hdr t.mem (off B o) l.W mx)
    (hia : word t.mem (off B o) (8 * sIfma) = off B a) : TCtx l t B Z o a mx sp sl ep eb := by
  have hn := hc.scr.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hlo := hc.lo
  have hk1 : ∀ r ∈ k1Ranges l.W, 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ slot l.W 8 := by
    have := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
    have := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
    have := slot_le (w := l.W) (show aT < 8 by decide)
    have := hdr_lt_slot l.W Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot l.W Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot l.W aT (show 31 < 32 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCtr, sFn] <;> omega_arith
  have hr : ∀ r ∈ shiftRanges o (k1Ranges l.W) ++ [(a + l.D * p, l.D)], o + 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ Z := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      have := hk1 r' hr'; simp only; omega_using [hoa, haZ, this]
    · rw [List.mem_singleton.mp hr]; simp only; omega_using [hoa, haZ, hDp, h16]
  have hw : ∀ d, d + 8 ≤ o + 8 * 30 → word t.mem B d = word s.mem B d := fun d hd =>
    word_below_frm hf (fun r h => (hr r h).1) hd (by omega_using [hoa, haZ, hn, h16])
  exact ⟨hc.scr.congr hwr, hdi, hH, hia,
    by rw [word_off, hw _ (by unfold sLink sFn; omega_using []), ← word_off]; exact hc.link,
    by rw [hw _ (by omega_using [hsp, h8, hlo])]; exact hpv,
    by rw [hw _ (by omega_using [hsl, h8, hlo])]; exact hlv,
    he.congr (InScr.of_frm hf fun r h => (hr r h).2) hrd hwr⟩

theorem tailR_disj (hl : LayOk l) {a p : Nat} {c : Nat} (hc : c + l.NB ≤ l.oK0 ∨ (l.oFin + l.NB ≤ c ∧ c + l.NB ≤ l.D) ∨
    (l.oK0 + 32 ≤ c ∧ c + l.NB ≤ l.oE) ∨ (l.oE + l.E ≤ c ∧ c + l.NB ≤ l.oFin)) :
    ∀ r ∈ tailR l a p, a + (l.D * p + c) + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ a + (l.D * p + c) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  simp only [tailR, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> simp only <;> omega_using [hc, o1, o6, o9]

/-- `region p`: prime `p`'s region of the area at `off B a`, from its
workspace at `off B o` (16 words). -/
theorem region_ok (hl : LayOk l) {s : State} {B : Addr} {Z o w a p X sp sl : Nat} {mx : BitVec 64} {ep : Addr}
    {eb : List Byte} (hc : SubCtx s B Z o w l.W mx) (hia : word s.mem (off B o) (8 * sIfma) = off B a)
    (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2)
    (hN : wv s.mem (off B o) (slot l.W Public.aN) l.W = X) (hY : wv s.mem (off B o) (slot l.W Public.aY) l.W < X)
    (hsp : sp < 32) (hsl : sl < 32) (hpv : word s.mem B (8 * sp) = ep)
    (hlv : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) (he : Src s B Z ep eb) (hL1 : 1 ≤ eb.length)
    (hL2 : eb.length ≤ l.E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (region l p sp sl)) s fun t =>
      RegOut l t.mem (off B a) p X (2 ^ l.dbls * wv s.mem (off B o) (slot l.W Public.aY) l.W % X)
        (wv s.mem (off B o) (slot l.W aXc) l.W) (wv s.mem (off B o) (slot l.W Public.aY) l.W)
        (if p = 0 then wv s.mem (off B o) (slot l.W Public.aY) l.W else 1) (mx &&& mask52) eb ∧
      Frm B (shiftRanges o (k1Ranges l.W) ++ [(a + l.D * p, l.D)]) s.mem t.mem ∧ t.wr = s.wr ∧
      t.gpr .rdi = off B o ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hoM : oM = 0 := rfl
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega_using []
  have hwide : ∀ q, q < 2 → ∀ r ∈ tailR l a q, ∃ r' ∈ shiftRanges o (k1Ranges l.W) ++ [(a + l.D * q, l.D)],
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun q hq r hr => ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
    by
      have hDq : l.D * q ≤ l.D := by rcases D_mul (l := l) hq with h | h <;> omega_using [h]
      simp only [tailR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_using [o9, o10, o1, o6]⟩
  have hY' : ∀ {t : State}, Frm B (shiftRanges o (k1Ranges l.W) ++ [(a + l.D * p, l.D)]) s.mem t.mem →
      wv t.mem (off B o) (slot l.W Public.aY) l.W = wv s.mem (off B o) (slot l.W Public.aY) l.W := fun hf => by
    have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
    have lY := slot_le (w := l.W) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]
    refine hf.wv_eq (fun r hr => ?_) (by omega_using [hoa, haZ, hn, lY])
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      rcases k1Ranges_arr (j := Public.aY) (by decide) (by decide) (by decide) r' hr' with h | h <;>
        simp only <;> omega_using [h]
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_using [hoa, lY])
  rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl
  · rw [show region l 0 sp sl = (k1 l ++ [.block (arr52 l 0 Public.aN oM),
      .block (arr52 l 0 aT l.oK1), .block (arr52 l 0 aXc l.oX), .block (arr52 l 0 Public.aY l.oY)]) ++
      ([.block (arr52 l 0 Public.aY l.oFin), .block (k0St l 0), .block (eZero l)] ++
      eCopy l sp sl) from rfl]
    refine wp_seqs_append (by simp [k1, copyArr]) (by simp) (WP.mono (regionA_ok hl hc hia hoa haZ hp hN hY)
      fun t ⟨lM, lK, lX, lY, fA, wA, dA, kA, _, hHA, iaA⟩ => ?_)
    refine WP.mono (regionB0_ok hl (TCtx.of_regionA hl hc hoa haZ hp hsp hsl hpv hlv he fA wA kA.2.1 dA hHA iaA) hoa haZ
      hsp hsl hL1 hL2) fun t' ⟨lF, hk, hE, fB, kB⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hk, hE⟩,
        fA.trans (fB.widen (hwide _ hp)), ?_, ?_, kA.trans kB |>.mono (by decide)⟩
    · exact lM.of_frm hl fB (tailR_disj hl (by omega_using [o1, hoM])) (by omega_using [haZ, hn, hDb1, hoM])
    · exact lK.of_frm hl fB (tailR_disj hl (by omega_using [o6, o7, o9])) (by omega_using [haZ, hn, o7, o10])
    · exact lX.of_frm hl fB (tailR_disj hl (by omega_using [o1, o3, o6])) (by omega_using [haZ, hn, o3, o10])
    · exact lY.of_frm hl fB (tailR_disj hl (by omega_using [o1, o2, o6])) (by omega_using [haZ, hn, o2, o10])
    · rw [hY' fA] at lF
      rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0))]
      exact lF
    · rw [kB.2.2, wA]
    · rw [kB.gpr (by decide), dA]
  · rw [show region l 1 sp sl = (k1 l ++ [.block (arr52 l 1 Public.aN oM),
      .block (arr52 l 1 aT l.oK1), .block (arr52 l 1 aXc l.oX), .block (arr52 l 1 Public.aY l.oY)]) ++
      ([.block (k0St l 1), .block (eZero l), .block (finOne l)] ++ eCopy l sp sl) from rfl]
    refine wp_seqs_append (by simp [k1, copyArr]) (by simp) (WP.mono (regionA_ok hl hc hia hoa haZ hp hN hY)
      fun t ⟨lM, lK, lX, lY, fA, wA, dA, kA, r12, hHA, iaA⟩ => ?_)
    refine WP.mono (regionB1_ok hl (TCtx.of_regionA hl hc hoa haZ hp hsp hsl hpv hlv he fA wA kA.2.1 dA hHA iaA) hoa haZ
      hsp hsl hL1 hL2 r12) fun t' ⟨lF, hk, hE, fB, kB⟩ => ⟨⟨?_, ?_, ?_, ?_, lF, hk, hE⟩,
        fA.trans (fB.widen (hwide _ hp)), ?_, ?_, kA.trans kB |>.mono (by decide)⟩
    · exact lM.of_frm hl fB (tailR_disj hl (by omega_using [o1, hoM])) (by omega_using [haZ, hn, hDb1, hoM])
    · exact lK.of_frm hl fB (tailR_disj hl (by omega_using [o6, o7, o9])) (by omega_using [haZ, hn, o7, o10])
    · exact lX.of_frm hl fB (tailR_disj hl (by omega_using [o1, o3, o6])) (by omega_using [haZ, hn, o3, o10])
    · exact lY.of_frm hl fB (tailR_disj hl (by omega_using [o1, o2, o6])) (by omega_using [haZ, hn, o2, o10])
    · rw [kB.2.2, wA]
    · rw [kB.gpr (by decide), dA]


end

end VG.Proof.Bignum.X86_64.Ifma
