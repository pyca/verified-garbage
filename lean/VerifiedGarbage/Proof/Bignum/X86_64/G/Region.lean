import VerifiedGarbage.Proof.Bignum.X86_64.G.VecR
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaRegion

/-!
# RSA with AVX512_IFMA on x86-64, any size: a prime's region

`IfmaRegion` for `CrtIfmaG`: `region` fills prime `p`'s region of the IFMA
area from its workspace: the modulus, `2^dbls R_X mod X`, the base and
`R_X` in the stride layout (`arr52_ok`), `k₀` (`k0St_ok`), the last
multiplier, and the exponent's bytes after zeros (`eCopy_ok`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside wv)
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (stMem stMem_outside word_stMem_other word_stMem limbN limbN_lt writeB_outside
  ofs_self writeB_self setWidth_byte' se_ofNat off_add)

variable {l : VG.Impl.Rsa.X86_64.CrtIfmaG.Lay}

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
  exact ⟨v, o', (k.trans k').mono (by simp), by rw [k'.gpr (by decide)]; exact r12, x'.trans mx⟩

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
    simp only [List.mem_map, List.mem_range]; rintro _ ⟨i, hi, rfl⟩; omega_arith
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
      · exact .inr (by omega_arith)) (fun d hd => by have := hlr d hd; omega_arith)
  · rw [← me]; exact stMem_outside _ _ _ (by omega_arith) _ hlr

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
    simp only [List.mem_map, List.mem_range]; rintro _ ⟨i, hi, rfl⟩; omega_arith
  rw [map_store (fun i => l.oE + 8 * i)]
  refine WP.mono (stRax_ok _ _ r11 ra fun d hd => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [k.2.2]; exact hwr i (List.mem_range.mp hi)) fun s' hs' => ?_
  subst hs'
  refine ⟨fun i hi' => ?_, by rw [← me]; exact stMem_outside _ _ _ (by omega_arith) _ hlr, ra, k, mx⟩
  exact word_stMem _ _ _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩) (fun d hd => by
    obtain ⟨i', hi'', rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hi''
    by_cases e : i' = i
    · exact .inl (by rw [e])
    · exact .inr (by omega_arith)) (fun d hd => by have := hlr d hd; omega_arith)

/-- `q`'s last multiplier: 1, in the limbs at `oFin` (`r11 = C`, `rax = 0`). -/
theorem finOne_ok (hl : LayOk l) {s : State} {C : Addr} (hC : s.gpr .r11 = C) (ha : s.gpr .rax = 0)
    (hF : l.oFin + l.NB < 2 ^ 31)
    (hwr : ∀ j < l.L, InRegions s.wr (C + BitVec.ofNat 64 (l.oFin + l.off j)) 8) :
    WP isa (.block (finOne l)) s fun s' =>
      (∀ j < l.L, word s'.mem C (l.oFin + l.off j) = BitVec.ofNat 64 (limbN 1 j)) ∧
      Outside C l.oFin l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hL0 : 0 < l.L := by have := hl.bounds; simp only [Lay.L]; omega
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
    have := off_lt hl hj; omega_arith
  refine ⟨fun j hj => ?_, ?_, ⟨fun r hr => k.gpr hr, k.2.1, k.2.2⟩, mx⟩
  · rw [me]
    by_cases e : j = 0
    · subst e
      rw [show l.off 0 = 0 by simp [Lay.off], Nat.add_zero]
      exact VG.Proof.Bignum.word_writeW_self _ _ _ _
    · have hs := off_sep hl (j := 0) (q := j) hL0 hj e
      have h00 : l.off 0 = 0 := by simp [Lay.off]
      rw [h00] at hs
      rw [(writeW_outside _ C _ (by omega_arith)).word (.inr (by omega_arith))
        (by have := hF' j hj; omega_arith)]
      rw [word_stMem _ _ _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          rw [List.mem_range] at hj'
          by_cases e' : j' = j
          · exact .inl (by rw [e'])
          · exact .inr (by have := off_sep hl hj hj' e'; omega_arith))
        (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          have := hF' j' (List.mem_range.mp hj'); omega_arith)]
      unfold limbN
      rw [Nat.div_eq_of_lt (Nat.one_lt_two_pow (by
        intro h; apply e; have : j = 0 := by omega
        exact this))]
      rfl
  · rw [me]
    exact (stMem_outside _ _ _ (by omega_arith) _ fun d hd => by
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
      exact ⟨by omega_arith, hF' j' (List.mem_range.mp hj')⟩).trans
      ((writeW_outside _ C _ (by omega_arith)).mono (by omega_arith) (by have := NB_le hl; omega_arith))

/-! ## The exponent's bytes -/

/-- The copy after `j` bytes. -/
structure CpInv (s₀ t : State) (C ep : Addr) (L : Nat) (eb : List Byte) (hL : eb.length = L) (j : Nat) :
    Prop where
  si : t.gpr .rsi = ep + BitVec.ofNat 64 j
  di : t.gpr .r11 = C + BitVec.ofNat 64 j
  cx : t.gpr .rcx = BitVec.ofNat 64 (L - j)
  bytes : ∀ i (h : i < L), i < j → t.mem (C + BitVec.ofNat 64 i) = eb[i]'(by omega_arith)
  out : Outside C 0 j s₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .r11] s₀ t
  mx : t.mxcsr = s₀.mxcsr

theorem cpStep_ok {s₀ t : State} {C ep : Addr} {L : Nat} {eb : List Byte} {hL : eb.length = L} {j : Nat}
    (hj : j < L) (hL2 : L < 2 ^ 31) (hI : CpInv s₀ t C ep L eb hL j)
    (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < L), s₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hwr : ∀ i < L, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1)
    (hsep : ∀ m m' : Mem, Outside C 0 L m m' → ∀ i < L,
      m' (ep + BitVec.ofNat 64 i) = m (ep + BitVec.ofNat 64 i)) :
    WP isa (.block [.movzx8 .rax (VG.Impl.Bignum.X86_64.at0 .rsi), .store8 (VG.Impl.Bignum.X86_64.at0 .r11) .rax,
      .alu .add .rsi (.imm 1), .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) t fun t' =>
      t'.zf = some (decide (j + 1 = L)) ∧ CpInv s₀ t' C ep L eb hL (j + 1) := by
  have hr : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hw : InRegions t.wr (C + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwr j hj
  have hb : t.mem (ep + BitVec.ofNat 64 j) = eb[j]'(by omega_arith) := by
    rw [hsep _ _ (hI.out.mono (Nat.le_refl _) (by omega_arith)) j hj]; exact hval j hj
  have e0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => BitVec.add_zero x
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t' =>
    t'.gpr .rsi = ep + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .r11 = C + BitVec.ofNat 64 (j + 1) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (L - (j + 1)) ∧ t'.zf = some (decide (j + 1 = L)) ∧
      t'.mem = t.mem.writeW (C + BitVec.ofNat 64 j) (eb[j]'(by omega_arith)) ∧ t'.mxcsr = t.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.at0, hI.si, hI.di, hI.cx, e0, hr, hw, hb]
      have e1 : BitVec.ofNat 64 (L - j) - 1 = BitVec.ofNat 64 (L - (j + 1)) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
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
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
          change _ = 0 at this
          omega_arith
      · rw [setWidth_byte']
      · rfl) rfl) fun t' ⟨⟨si, di, cx, zf, me, mx⟩, k⟩ => ⟨zf, si, di, cx, fun i hiL hi => ?_, ?_,
        (hI.keep.trans k).mono (by simp), mx.trans hI.mx⟩
  · have ow := writeB_outside t.mem C (d := j) (eb[j]'(by omega_arith)) (by omega_arith)
    rw [me]
    by_cases e : i = j
    · subst e; exact (writeB_self _ _ _).trans rfl
    · rw [ow _ (by rw [ofs_self C (by omega_arith)]; omega_arith)]
      exact hI.bytes i hiL (by omega_arith)
  · rw [me]
    exact (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeB_outside t.mem C (d := j) (eb[j]'(by omega_arith)) (by omega_arith)).mono (by omega_arith)
        (by omega_arith))

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
    (hval : ∀ i (h : i < L), s.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hwr : ∀ i < L, InRegions s.wr (off C (l.oE + l.E - L) + BitVec.ofNat 64 i) 1)
    (hsep : ∀ m m' : Mem, Outside (off C (l.oE + l.E - L)) 0 L m m' → ∀ i < L,
      m' (ep + BitVec.ofNat 64 i) = m (ep + BitVec.ofNat 64 i)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (eCopy l sp sl)) s fun s' =>
      (∀ i (h : i < L), s'.mem (off C (l.oE + l.E - L) + BitVec.ofNat 64 i) = eb[i]'(by omega_arith)) ∧
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
          VG.Offset.add_ofNat_sub _ (by omega_arith)]
      · exact hlv'
      all_goals rfl) rfl) fun s₁ ⟨⟨si, di, cx, me, mx⟩, k⟩ => ?_)
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  refine wp_upto (a := 0) (N := L) (by omega_arith)
    (fun j t => CpInv s₁ t (off C (l.oE + l.E - L)) ep L eb hL j)
    (fun j _ hj t hI => cpStep_ok hj (by omega_arith) hI (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi)
      (fun i hi => by rw [me]; exact hval i hi) (fun i hi => by rw [k.2.2]; exact hwr i hi) hsep)
    (fun t hI => ⟨fun i hi => hI.bytes i hi hi, by rw [← me]; exact hI.out, (k.trans hI.keep).mono (by simp),
      hI.mx.trans mx⟩) ⟨by rw [e0]; exact si, by rw [e0]; exact di, by rw [Nat.sub_zero]; exact cx,
      fun _ _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩

end VG.Proof.Bignum.X86_64.G
