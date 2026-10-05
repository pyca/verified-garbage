import VerifiedGarbage.Proof.Bignum.X86_64.IfmaConv
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPre

/-!
# RSA with AVX512_IFMA on x86-64: a prime's region

`region` fills prime `p`'s region of the IFMA area from its workspace: the
modulus, `2¹⁰⁵⁶ mod X`, the base and `R` in the vector layout (`arr52_ok`),
`k₀` (`k0St_ok`), the last multiplier, and the exponent's bytes after zeros
(`eCopy_ok`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off writeW_outside wv)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oTab oS oV oX oY oE oFin oMx mask52)

/-! ## Stores of `rax` -/

/-- `v` written at `C` plus each offset of `l` in turn. -/
def stMem (m : Mem) (C : Addr) (v : BitVec 64) : List Nat → Mem
  | [] => m
  | d :: l => stMem (m.writeW (off C d) v) C v l

theorem stRax_ok {C : Addr} {v : BitVec 64} :
    ∀ (l : List Nat) (s : State), s.gpr .r11 = C → s.gpr .rax = v →
      (∀ d ∈ l, InRegions s.wr (C + BitVec.ofNat 64 d) 8) →
      WP isa (.block (l.map fun d => .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 d) .rax)) s
        fun s' => s' = { s with mem := stMem s.mem C v l }
  | [], s, _, _, _ => WP.block_nil rfl
  | d :: rest, s, hC, hv, hw => by
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off C d) v }, ?_, ?_⟩
    · simp only [exec, ea_at', hC, hv, State.store64, hw d (List.mem_cons_self ..), ite_true, off]
    · exact WP.mono (stRax_ok rest _ hC hv fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => h

theorem map_store (f : Nat → Nat) (l : List Nat) :
    l.map (fun x => Instr.store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (f x)) .rax) =
      (l.map f).map (fun d => .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 d) .rax) := by
  simp only [List.map_map, Function.comp_def]

theorem stMem_outside (m : Mem) (C : Addr) (v : BitVec 64) {lo n : Nat} (hn : lo + n ≤ 2 ^ 64) :
    ∀ l : List Nat, (∀ d ∈ l, lo ≤ d ∧ d + 8 ≤ lo + n) → Outside C lo n m (stMem m C v l)
  | [], _ => Outside.refl _ _ _ _
  | d :: l, h => by
    have hd := h d (List.mem_cons_self ..)
    exact ((writeW_outside m C v (by omega)).mono (by omega) (by omega)).trans
      (stMem_outside _ C v hn l fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A word the writes miss. -/
theorem word_stMem_other (C : Addr) (v : BitVec 64) {e : Nat} (he : e + 8 ≤ 2 ^ 64) :
    ∀ (l : List Nat) (m : Mem), (∀ d ∈ l, d + 8 ≤ e ∨ e + 8 ≤ d) → (∀ d ∈ l, d + 8 ≤ 2 ^ 64) →
      word (stMem m C v l) C e = word m C e
  | [], _, _, _ => rfl
  | d :: l, m, h, h' => by
    rw [stMem, word_stMem_other C v he l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (fun x hx => h' x (List.mem_cons_of_mem _ hx))]
    exact (writeW_outside m C v (h' d (List.mem_cons_self ..))).word (h d (List.mem_cons_self ..)).symm he

/-- A word written, which no other write overlaps. -/
theorem word_stMem (C : Addr) (v : BitVec 64) {e : Nat} :
    ∀ (l : List Nat) (m : Mem), e ∈ l → (∀ d ∈ l, d = e ∨ d + 8 ≤ e ∨ e + 8 ≤ d) →
      (∀ d ∈ l, d + 8 ≤ 2 ^ 64) → word (stMem m C v l) C e = v
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | d :: l, m, h, hs, h' => by
    have h'' : ∀ x ∈ l, x + 8 ≤ 2 ^ 64 := fun x hx => h' x (List.mem_cons_of_mem _ hx)
    by_cases hl : e ∈ l
    · exact word_stMem C v l _ hl (fun x hx => hs x (List.mem_cons_of_mem _ hx)) h''
    · have hd : d = e := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h hl
      subst hd
      rw [stMem, word_stMem_other C v (h' d (List.mem_cons_self ..)) l _ (fun x hx => by
        rcases hs x (List.mem_cons_of_mem _ hx) with h | h
        · exact absurd (h ▸ hx) hl
        · exact h) h'']
      exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _

/-- A frame at `B + o` as one at `B`. -/
theorem Outside.rebase {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside (off B o) 0 n m m')
    (ho : o < 2 ^ 64) (hn : o + n ≤ 2 ^ 64) : Outside B o n m m' := fun x hx => h x (by
  rcases ofs_rebase' B x ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inr (by omega)
  · exact .inr (by omega))

/-! ## Arrays into the vector layout -/

/-- Array `j` of the prime's workspace `W` (`Aj`) into the limbs at `o` of
region `p` of the area `A`. -/
theorem arr52_ok {s : State} {W A Aj : Addr} {p j o : Nat} (hdi : s.gpr .rdi = W)
    (hH : ∀ i < 32, InRegions (s.rd ++ s.wr) (off W (8 * i)) 8) (hjs : VG.Impl.Bignum.X86_64.sArr j < 32)
    (hj : word s.mem W (8 * VG.Impl.Bignum.X86_64.sArr j) = Aj)
    (hA : word s.mem W (8 * VG.Impl.Rsa.X86_64.CrtIfma.sIfma) = A) (hc : D * p + o < 2 ^ 31)
    (hrd : ∀ i < 16, InRegions (s.rd ++ s.wr) (Aj + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : ∀ k < 20, InRegions s.wr (off A (D * p + o) + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.off k)) 8)
    (hsep : ∀ m m' : Mem, Outside (off A (D * p + o)) 0 160 m m' → ∀ i < 16, word m' Aj (8 * i) = word m Aj (8 * i)) :
    WP isa (.block (VG.Impl.Rsa.X86_64.CrtIfma.arr52 p j o)) s fun s' =>
      (∀ k < 20, word s'.mem (off A (D * p + o)) (VG.Impl.Rsa.X86_64.CrtIfma.off k) =
        BitVec.ofNat 64 (limbN (wv s.mem Aj 0 16) k)) ∧
      Outside (off A (D * p + o)) 0 160 s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] s s' ∧ s'.gpr .r12 = mask52 ∧
      s'.mxcsr = s.mxcsr := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.arr52
  rw [WP.block_append_iff]
  have l1 := hH _ hjs
  have l2 := hH VG.Impl.Rsa.X86_64.CrtIfma.sIfma (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rsi, .r11, .r12] (Q := fun t => t.gpr .rsi = Aj ∧
    t.gpr .r11 = off A (D * p + o) ∧ t.gpr .r12 = mask52 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, l1, l2, se_ofNat hc]
      and_intros
      · exact hj
      · exact congrArg (· + BitVec.ofNat 64 (D * p + o)) hA
      all_goals rfl) rfl) fun t ⟨⟨si, r11, r12, me, mx⟩, k⟩ => ?_
  refine WP.mono (to52_ok si r11 r12 (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi)
    (fun i hi => by rw [k.2.2]; exact hwr i hi) hsep) fun s' ⟨v, o', k', x'⟩ => ?_
  rw [me] at v o'
  exact ⟨v, o', (k.trans k').mono (by simp), by rw [k'.gpr (by decide)]; exact r12, x'.trans mx⟩

/-! ## `k₀`, zeros and the last multiplier -/

/-- `k₀ = minv mod 2⁵²` in the four quadwords at `oK0` of region `p` (`r11 := C`, its base). -/
theorem k0St_ok {s : State} {W A : Addr} {p : Nat} {minv : BitVec 64} (hdi : s.gpr .rdi = W)
    (hH : ∀ i < 32, InRegions (s.rd ++ s.wr) (off W (8 * i)) 8)
    (hA : word s.mem W (8 * VG.Impl.Rsa.X86_64.CrtIfma.sIfma) = A)
    (hm : word s.mem W (8 * VG.Impl.Bignum.X86_64.sMinv) = minv) (h12 : s.gpr .r12 = mask52) (hc : D * p < 2 ^ 31)
    (hwr : ∀ t < 4, InRegions s.wr (off A (D * p) + BitVec.ofNat 64 (oK0 + 8 * t)) 8) :
    WP isa (.block (VG.Impl.Rsa.X86_64.CrtIfma.k0St p)) s fun s' =>
      (∀ t < 4, word s'.mem (off A (D * p)) (oK0 + 8 * t) = minv &&& mask52) ∧
      Outside (off A (D * p)) oK0 32 s.mem s'.mem ∧ s'.gpr .r11 = off A (D * p) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.k0St
  rw [WP.block_append_iff]
  have l1 := hH VG.Impl.Rsa.X86_64.CrtIfma.sIfma (by decide)
  have l2 := hH VG.Impl.Bignum.X86_64.sMinv (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .r11] (Q := fun t =>
    t.gpr .r11 = off A (D * p) ∧ t.gpr .rax = minv &&& mask52 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, l1, l2, se_ofNat hc, h12]
      and_intros
      · exact congrArg (· + BitVec.ofNat 64 (D * p)) hA
      · exact congrArg (· &&& mask52) hm
      all_goals rfl) rfl) fun t ⟨⟨r11, ra, me, mx⟩, k⟩ => ?_
  have hl : ∀ d ∈ (List.range 4).map (fun l => oK0 + 8 * l), oK0 ≤ d ∧ d + 8 ≤ oK0 + 32 := by
    simp only [List.mem_map, List.mem_range, oK0]; rintro _ ⟨l, hl, rfl⟩; omega
  rw [map_store (fun l => oK0 + 8 * l)]
  refine WP.mono (stRax_ok _ t r11 ra fun d hd => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    rw [k.2.2]; exact hwr l (List.mem_range.mp hl)) fun s' hs' => ?_
  subst hs'
  refine ⟨fun l hl' => ?_, ?_, r11, k, mx⟩
  · exact word_stMem _ _ _ _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl', rfl⟩) (fun d hd => by
      obtain ⟨l', hl'', rfl⟩ := List.mem_map.mp hd
      rw [List.mem_range] at hl''
      by_cases e : l' = l
      · exact .inl (by rw [e])
      · exact .inr (by omega)) (fun d hd => by have := hl d hd; simp only [oK0] at this; omega)
  · rw [← me]; exact stMem_outside _ _ _ (by simp only [oK0]; omega) _ hl

/-- Zeros in the sixteen quadwords at `oE` (`r11 = C`). -/
theorem eZero_ok {s : State} {C : Addr} (hC : s.gpr .r11 = C)
    (hwr : ∀ l < 16, InRegions s.wr (C + BitVec.ofNat 64 (oE + 8 * l)) 8) :
    WP isa (.block VG.Impl.Rsa.X86_64.CrtIfma.eZero) s fun s' =>
      (∀ l < 16, word s'.mem C (oE + 8 * l) = 0) ∧ Outside C oE 128 s.mem s'.mem ∧ s'.gpr .rax = 0 ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [show VG.Impl.Rsa.X86_64.CrtIfma.eZero = [.mov32 .rax (.imm 0)] ++
    (List.range 16).map (fun l => .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (oE + 8 * l)) .rax) from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = 0 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by xrun; and_intros; all_goals rfl) rfl)
    fun t ⟨⟨ra, me, mx⟩, k⟩ => ?_
  have r11 : t.gpr .r11 = C := by rw [k.gpr (by decide)]; exact hC
  have hl : ∀ d ∈ (List.range 16).map (fun l => oE + 8 * l), oE ≤ d ∧ d + 8 ≤ oE + 128 := by
    simp only [List.mem_map, List.mem_range, oE]; rintro _ ⟨l, hl, rfl⟩; omega
  rw [map_store (fun l => oE + 8 * l)]
  refine WP.mono (stRax_ok _ _ r11 ra fun d hd => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    rw [k.2.2]; exact hwr l (List.mem_range.mp hl)) fun s' hs' => ?_
  subst hs'
  refine ⟨fun l hl' => ?_, by rw [← me]; exact stMem_outside _ _ _ (by simp only [oE]; omega) _ hl, ra, k, mx⟩
  exact word_stMem _ _ _ _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl', rfl⟩) (fun d hd => by
    obtain ⟨l', hl'', rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hl''
    by_cases e : l' = l
    · exact .inl (by rw [e])
    · exact .inr (by omega)) (fun d hd => by have := hl d hd; simp only [oE] at this; omega)

/-- `q`'s last multiplier: 1, in the limbs at `oFin` (`r11 = C`, `rax = 0`). -/
theorem finOne_ok {s : State} {C : Addr} (hC : s.gpr .r11 = C) (ha : s.gpr .rax = 0)
    (hwr : ∀ j < 20, InRegions s.wr (C + BitVec.ofNat 64 (oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j)) 8) :
    WP isa (.block VG.Impl.Rsa.X86_64.CrtIfma.finOne) s fun s' =>
      (∀ j < 20, word s'.mem C (oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j) = BitVec.ofNat 64 (limbN 1 j)) ∧
      Outside C oFin 160 s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.finOne
  rw [WP.block_append_iff, map_store (fun j => oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j)]
  have hl : ∀ d ∈ (List.range 20).map (fun j => oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j),
      ∃ j < 20, d = oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j := by
    simp only [List.mem_map, List.mem_range]; rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  refine WP.mono (stRax_ok _ _ hC ha fun d hd => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    exact hwr j (List.mem_range.mp hj)) fun t ht => ?_
  subst ht
  have h0 : InRegions s.wr (C + BitVec.ofNat 64 oFin) 8 := hwr 0 (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t' =>
    t'.mem = (stMem s.mem C 0 ((List.range 20).map fun j => oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j)).writeW
      (off C oFin) (1 : BitVec 64) ∧ t'.mxcsr = s.mxcsr) (by
      xrun [ea_at', hC, h0]
      and_intros
      all_goals rfl) rfl) fun s' ⟨⟨me, mx⟩, k⟩ => ?_
  have hF : ∀ j < 20, oFin + VG.Impl.Rsa.X86_64.CrtIfma.off j + 8 ≤ oFin + 160 := fun j hj => by
    rw [off_lim]; omega
  refine ⟨fun j hj => ?_, ?_, ⟨fun r hr => k.gpr hr, k.2.1, k.2.2⟩, mx⟩
  · rw [me]
    by_cases e : j = 0
    · subst e
      exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
    · rw [(writeW_outside _ C _ (by simp only [oFin]; omega)).word (.inr (by rw [off_lim]; omega))
        (by have := hF j hj; simp only [oFin] at this ⊢; omega)]
      rw [word_stMem _ _ _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          rw [List.mem_range] at hj'
          by_cases e' : j' = j
          · exact .inl (by rw [e'])
          · exact .inr (by rw [off_lim, off_lim]; omega))
        (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          have := hF j' (List.mem_range.mp hj'); simp only [oFin] at this ⊢; omega)]
      unfold limbN
      rw [Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      rfl
  · rw [me]
    exact (stMem_outside _ _ _ (by simp only [oFin]; omega) _ fun d hd => by
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
      exact ⟨by omega, hF j' (List.mem_range.mp hj')⟩).trans
      ((writeW_outside _ C _ (by simp only [oFin]; omega)).mono (by omega) (by simp only [oFin]; omega))

/-! ## The exponent's bytes -/

theorem writeB_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem ofs_self (C : Addr) {i : Nat} (h : i < 2 ^ 64) : ofs C (C + BitVec.ofNat 64 i) = i := by
  rw [ofs, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem writeB_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero]
  ext i hi; simp

theorem setWidth_byte' (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

/-- The copy after `j` bytes. -/
structure CpInv (s₀ t : State) (C ep : Addr) (L : Nat) (eb : List Byte) (hL : eb.length = L) (j : Nat) : Prop where
  si : t.gpr .rsi = ep + BitVec.ofNat 64 j
  di : t.gpr .r11 = C + BitVec.ofNat 64 j
  cx : t.gpr .rcx = BitVec.ofNat 64 (L - j)
  bytes : ∀ i (h : i < L), i < j → t.mem (C + BitVec.ofNat 64 i) = eb[i]'(by omega)
  out : Outside C 0 j s₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .r11] s₀ t
  mx : t.mxcsr = s₀.mxcsr

theorem cpStep_ok {s₀ t : State} {C ep : Addr} {L : Nat} {eb : List Byte} {hL : eb.length = L} {j : Nat}
    (hj : j < L) (hL2 : L ≤ 128) (hI : CpInv s₀ t C ep L eb hL j)
    (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < L), s₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hwr : ∀ i < L, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1)
    (hsep : ∀ m m' : Mem, Outside C 0 L m m' → ∀ i < L, m' (ep + BitVec.ofNat 64 i) = m (ep + BitVec.ofNat 64 i)) :
    WP isa (.block [.movzx8 .rax (VG.Impl.Bignum.X86_64.at0 .rsi), .store8 (VG.Impl.Bignum.X86_64.at0 .r11) .rax,
      .alu .add .rsi (.imm 1), .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) t fun t' =>
      t'.zf = some (decide (j + 1 = L)) ∧ CpInv s₀ t' C ep L eb hL (j + 1) := by
  have hr : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hw : InRegions t.wr (C + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwr j hj
  have hb : t.mem (ep + BitVec.ofNat 64 j) = eb[j]'(by omega) := by
    rw [hsep _ _ (hI.out.mono (Nat.le_refl _) (by omega)) j hj]; exact hval j hj
  have e0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => BitVec.add_zero x
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t' =>
    t'.gpr .rsi = ep + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .r11 = C + BitVec.ofNat 64 (j + 1) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (L - (j + 1)) ∧ t'.zf = some (decide (j + 1 = L)) ∧
      t'.mem = t.mem.writeW (C + BitVec.ofNat 64 j) (eb[j]'(by omega)) ∧ t'.mxcsr = t.mxcsr) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.at0, hI.si, hI.di, hI.cx, e0, hr, hw, hb]
      have e1 : BitVec.ofNat 64 (L - j) - 1 = BitVec.ofNat 64 (L - (j + 1)) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega)]
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
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          change _ = 0 at this
          omega
      · rw [setWidth_byte']
      · rfl) rfl) fun t' ⟨⟨si, di, cx, zf, me, mx⟩, k⟩ => ⟨zf, si, di, cx, fun i hiL hi => ?_, ?_,
        (hI.keep.trans k).mono (by simp), mx.trans hI.mx⟩
  · have ow := writeB_outside t.mem C (d := j) (eb[j]'(by omega)) (by omega)
    rw [me]
    by_cases e : i = j
    · subst e; exact (writeB_self _ _ _).trans rfl
    · rw [ow _ (by rw [ofs_self C (by omega)]; omega)]
      exact hI.bytes i hiL (by omega)
  · rw [me]
    exact (hI.out.mono (Nat.le_refl _) (by omega)).trans
      ((writeB_outside t.mem C (d := j) (eb[j]'(by omega)) (by omega)).mono (by omega) (by omega))

/-- The exponent's `L` bytes (`eb`, at `ep`, the pointer and length in the
slots `sp` and `sl` of `n`'s workspace `B`) at the end of the 128 at `oE` of
the region at `C` (`r11`). -/
theorem eCopy_ok {s : State} {W B C ep : Addr} {L sp sl : Nat} {eb : List Byte} (hL : eb.length = L)
    (hL1 : 1 ≤ L) (hL2 : L ≤ 128) (hdi : s.gpr .rdi = W) (hC : s.gpr .r11 = C)
    (hlk : InRegions (s.rd ++ s.wr) (off W (8 * VG.Impl.Rsa.X86_64.Crt.sLink)) 8)
    (hlv : word s.mem W (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = B)
    (hp : InRegions (s.rd ++ s.wr) (off B (8 * sp)) 8) (hl : InRegions (s.rd ++ s.wr) (off B (8 * sl)) 8)
    (hpv : word s.mem B (8 * sp) = ep) (hlv' : word s.mem B (8 * sl) = BitVec.ofNat 64 L)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < L), s.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hwr : ∀ i < L, InRegions s.wr (off C (oE + 128 - L) + BitVec.ofNat 64 i) 1)
    (hsep : ∀ m m' : Mem, Outside (off C (oE + 128 - L)) 0 L m m' → ∀ i < L,
      m' (ep + BitVec.ofNat 64 i) = m (ep + BitVec.ofNat 64 i)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (VG.Impl.Rsa.X86_64.CrtIfma.eCopy sp sl)) s fun s' =>
      (∀ i (h : i < L), s'.mem (off C (oE + 128 - L) + BitVec.ofNat 64 i) = eb[i]'(by omega)) ∧
      Outside (off C (oE + 128 - L)) 0 L s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.eCopy
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t =>
    t.gpr .rsi = ep ∧ t.gpr .r11 = off C (oE + 128 - L) ∧ t.gpr .rcx = BitVec.ofNat 64 L ∧ t.mem = s.mem ∧
      t.mxcsr = s.mxcsr) (by
      have hlv₁ : s.mem.readW (off W (8 * VG.Impl.Rsa.X86_64.Crt.sLink)) 64 = B := hlv
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdi, hdrOff, hlk, hlv₁, hp, hl,
        se_ofNat (show oE + 128 < 2 ^ 31 by simp only [oE]; omega)]
      and_intros
      · exact hpv
      · rw [show s.mem.readW (off B (8 * sl)) 64 = BitVec.ofNat 64 L from hlv', hC,
          VG.Offset.add_ofNat_sub _ (by simp only [oE]; omega)]
      · exact hlv'
      all_goals rfl) rfl) fun s₁ ⟨⟨si, di, cx, me, mx⟩, k⟩ => ?_)
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  refine wp_upto (a := 0) (N := L) (by omega) (fun j t => CpInv s₁ t (off C (oE + 128 - L)) ep L eb hL j)
    (fun j _ hj t hI => cpStep_ok hj hL2 hI (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi)
      (fun i hi => by rw [me]; exact hval i hi) (fun i hi => by rw [k.2.2]; exact hwr i hi) hsep)
    (fun t hI => ⟨fun i hi => hI.bytes i hi hi, by rw [← me]; exact hI.out, (k.trans hI.keep).mono (by simp),
      hI.mx.trans mx⟩) ⟨by rw [e0]; exact si, by rw [e0]; exact di, by rw [Nat.sub_zero]; exact cx,
      fun _ _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-! ## `2¹⁰⁵⁶ mod X` -/

/-- The ranges `k1` writes in the prime's workspace. -/
def k1Ranges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx Public.aAcc, 8 * (wx + 2)), (slot wx Public.aTmp, 8 * (wx + 2)),
    (slot wx VG.Impl.Rsa.X86_64.Crt.aT, 8 * (wx + 2)), (8 * VG.Impl.Rsa.X86_64.CrtIfma.sCtr, 8)]

/-- `aT := 2³² [aY] mod X` in the prime's workspace `W`. -/
theorem k1_ok {s : State} {W : Addr} {wx : Nat} {minv : BitVec 64} {X : Nat}
    (hg : Good s W (slot wx 8) wx minv) (hw2 : 2 ≤ wx) (hw' : wx < 2 ^ 31)
    (hN : wv s.mem W (slot wx Public.aN) wx = X) (hY : wv s.mem W (slot wx Public.aY) wx < X) :
    WP isa (VG.Impl.Bignum.X86_64.seqs VG.Impl.Rsa.X86_64.CrtIfma.k1) s fun t =>
      wv t.mem W (slot wx VG.Impl.Rsa.X86_64.Crt.aT) wx = 2 ^ 32 * wv s.mem W (slot wx Public.aY) wx % X ∧
      Frm W (k1Ranges wx) s.mem t.mem ∧ Hdr t.mem W wx minv ∧ Keep mmRegs s t := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.k1
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) hw'
    (o := VG.Impl.Rsa.X86_64.Crt.aT) (a := Public.aY) (by decide) (by decide) (by decide))
    fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_)
  have hn := hg.scr.nowrap
  have lT := slot_le (w := wx) (show VG.Impl.Rsa.X86_64.Crt.aT < 8 by decide)
  have lN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have sTN := slot_sep (w := wx) (show VG.Impl.Rsa.X86_64.Crt.aT ≠ Public.aN by decide)
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ : wv s₁.mem W (slot wx Public.aN) wx = X := by rw [ho₁.wv (by omega) (by omega)]; exact hN
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 32 ∧ t.mem = s₁.mem) (by
    xrun; and_intros) rfl) fun s₂ ⟨⟨cx₂, me₂⟩, k₂⟩ => ?_)
  have hg₂ : Good s₂ W (slot wx 8) wx minv := by
    refine ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ?_⟩
    rw [me₂]; exact hg₁.hdr
  refine WP.mono (doubles_ok hg₂.scr hg₂.rdi hg₂.hdr (Nat.le_refl _) hw2 hw' (mo := Public.aN)
    (acc := Public.aAcc) (tmp := Public.aTmp) (o := VG.Impl.Rsa.X86_64.Crt.aT)
    (sl := VG.Impl.Rsa.X86_64.CrtIfma.sCtr) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (c := 32) (by decide)
    (by decide) cx₂ (by rw [me₂, hv₁, hN₁]; exact hY)) fun t ⟨hv, hf, hH, k⟩ => ⟨?_, ?_, hH, ?_⟩
  · rw [hv, me₂, hN₁, hv₁]
  · exact (Frm.of_outside (ho₁.mono (o' := slot wx VG.Impl.Rsa.X86_64.Crt.aT) (n' := 8 * (wx + 2))
      (Nat.le_refl _) (by omega)) (by simp [k1Ranges])).trans (by rw [← me₂]; exact hf)
  · exact ((k₁.trans k₂).trans k).mono (by decide)

/-! ## Facts about the area that the region's steps carry -/

/-- The twenty limbs of `v` at offset `e` of the area `F`. -/
def Limbs (m : Mem) (F : Addr) (e v : Nat) : Prop :=
  ∀ k < 20, word m F (e + CrtIfma.off k) = BitVec.ofNat 64 (AmmSym.limbN v k)

theorem off_lt160 {k : Nat} (hk : k < 20) : CrtIfma.off k + 8 ≤ 160 := by
  rw [AmmSym.off_lim]; omega

theorem Limbs.of_frm {m m' : Mem} {B : Addr} {a e v : Nat} {rs : List (Nat × Nat)} (h : Limbs m (off B a) e v)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, a + e + 160 ≤ r.1 ∨ r.1 + r.2 ≤ a + e) (hz : a + e + 160 ≤ 2 ^ 64) :
    Limbs m' (off B a) e v := fun k hk => by
  have := off_lt160 hk
  rw [word_off, hf.word_eq (fun r hr => by rcases hd r hr with h | h <;> omega) (by omega), ← word_off]
  exact h k hk

theorem byte_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} (hf : Frm B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 1 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hz : d < 2 ^ 64) : m' (off B d) = m (off B d) :=
  hf _ fun r hr => by rw [AmmSym.ofs_off0 B hz]; rcases hd r hr with h | h <;> omega

/-- `arr52` in a prime's workspace (`rdi = off B o`, 16 words), the area at `off B a`. -/
theorem arr52r_ok {t : State} {B : Addr} {Z o a p j c : Nat} {mx : BitVec 64} (hs : Scr t B Z)
    (hdi : t.gpr .rdi = off B o) (hH : Hdr t.mem (off B o) 16 mx)
    (hia : word t.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2) (hc : c + 160 ≤ D) (hj : j < 8) :
    WP isa (.block (CrtIfma.arr52 p j c)) t fun t' =>
      Limbs t'.mem (off B a) (D * p + c) (wv t.mem (off B o) (slot 16 j) 16) ∧
      Frm B [(a + (D * p + c), 160)] t.mem t'.mem ∧
      Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] t t' ∧ t'.gpr .r12 = mask52 ∧ t'.mxcsr = t.mxcsr := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have lj := slot_le (w := 16) hj
  have hT : tabBytes 16 = 2304 := rfl
  have hH' : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot 16 8 hi; omega)
  refine WP.mono (AmmSym.arr52_ok (A := off B a) (Aj := off (off B o) (slot 16 j)) hdi hH'
    (by unfold sArr; omega) (hH.harr j hj) hia (by omega)
    (fun i hi => by rw [off_off, AmmSym.off_add]; exact hs.ld (by omega))
    (fun k hk => by
      have := off_lt160 hk
      rw [off_off, AmmSym.off_add]; exact hs.st (by omega))
    (fun m m' ho i hi => by
      rw [off_off] at ho
      rw [off_off, word_off, word_off]
      exact (Frm.of_outside_off ho (by omega) (by omega)).word_eq
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)) (by omega)))
    fun t' ⟨hv, ho, k, h12, hx⟩ => ⟨fun k hk => ?_, ?_, k, h12, hx⟩
  · rw [← word_off, hv k hk, wv_off, Nat.add_zero]
  · rw [off_off] at ho
    have := Frm.of_outside_off ho (by omega) (by omega)
    simpa only [Nat.add_zero] using this

theorem word_below_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} {L : Nat} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, L ≤ r.1) {d : Nat} (hd : d + 8 ≤ L) (hz : L ≤ 2 ^ 64) : word m' B d = word m B d :=
  hf.word_eq (fun r h => .inl (by have := hr r h; omega)) (by omega)

theorem Hdr.of_below {m m' : Mem} {B : Addr} {o wx : Nat} {mx : BitVec 64} (hH : Hdr m (off B o) wx mx)
    {rs : List (Nat × Nat)} (hf : Frm B rs m m') (hr : ∀ r ∈ rs, o + hdrBytes ≤ r.1)
    (hz : o + hdrBytes ≤ 2 ^ 64) : Hdr m' (off B o) wx mx := by
  have hh : ∀ i < 32, word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact word_below_frm hf hr (by unfold hdrBytes; omega) hz
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

theorem wv_below_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} {L : Nat} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, L ≤ r.1) {d k : Nat} (hd : d + 8 * k ≤ L) (hz : L ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  hf.wv_eq (fun r h => .inl (by have := hr r h; omega)) (by omega)

/-- `arr52` after earlier changes within region `p`, from `s₁`. -/
theorem arrA_ok {s₁ t : State} {B : Addr} {Z o a p j c : Nat} {mx : BitVec 64} (hs : Scr s₁ B Z)
    (hdi : s₁.gpr .rdi = off B o) (hH : Hdr s₁.mem (off B o) 16 mx)
    (hia : word s₁.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2) (hc : c + 160 ≤ D) (hj : j < 8)
    (hf : Frm B [(a + D * p, D)] s₁.mem t.mem) (hwr : t.wr = s₁.wr) (hdt : t.gpr .rdi = s₁.gpr .rdi) :
    WP isa (.block (CrtIfma.arr52 p j c)) t fun t' =>
      Limbs t'.mem (off B a) (D * p + c) (wv s₁.mem (off B o) (slot 16 j) 16) ∧
      Frm B [(a + D * p, D)] s₁.mem t'.mem ∧ Frm B [(a + (D * p + c), 160)] t.mem t'.mem ∧
      t'.wr = s₁.wr ∧ t'.gpr .rdi = s₁.gpr .rdi ∧
      Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] t t' ∧ t'.gpr .r12 = mask52 := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have lj := slot_le (w := 16) hj
  have hT : tabBytes 16 = 2304 := rfl
  have hr : ∀ r ∈ [(a + D * p, D)], a ≤ r.1 := fun r h => by rw [List.mem_singleton.mp h]; simp only; omega
  have hia' : word t.mem (off B o) (8 * sIfma) = off B a := by
    rw [word_off, word_below_frm hf hr (by unfold sIfma sFn; omega) (by omega), ← word_off]; exact hia
  have hwv : wv t.mem (off B o) (slot 16 j) 16 = wv s₁.mem (off B o) (slot 16 j) 16 := by
    rw [wv_off, wv_off, wv_below_frm hf hr (by omega) (by omega)]
  refine WP.mono (arr52r_ok (hs.congr hwr) (hdt.trans hdi)
    (hH.of_below hf (fun r h => by have := hr r h; unfold hdrBytes; unfold slot hdrBytes at h8; omega)
      (by unfold hdrBytes; omega)) hia' hoa haZ hp hc hj)
    fun t' ⟨hv, f', k, h12, _⟩ => ⟨by rw [hwv] at hv; exact hv, ?_, f', ?_, ?_, k, h12⟩
  · exact hf.trans (f'.widen fun r h => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp h]; simp only; omega⟩)
  · rw [k.2.2, hwr]
  · rw [k.gpr (by decide), hdt]

/-- `k1`'s ranges miss an array of the prime but `aAcc`, `aTmp`, `aT`. -/
theorem k1Ranges_arr {j : Nat} (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ aT) :
    ∀ r ∈ k1Ranges 16, slot 16 j + 8 * 16 ≤ r.1 ∨ r.1 + r.2 ≤ slot 16 j := by
  have := slot_sep (w := 16) h1
  have := slot_sep (w := 16) h2
  have := slot_sep (w := 16) h3
  have := hdr_lt_slot 16 j (show CrtIfma.sCtr < 32 by decide)
  simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [CrtIfma.sCtr, sFn] at * <;> omega

/-- `region`'s start: `2¹⁰⁵⁶ mod X` into `aT`, then the modulus, it, `x R`
and `R` into region `p`. -/
theorem regionA_ok {s : State} {B : Addr} {Z o w a p X : Nat} {mx : BitVec 64} (hc : SubCtx s B Z o w 16 mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2) (hN : wv s.mem (off B o) (slot 16 Public.aN) 16 = X)
    (hY : wv s.mem (off B o) (slot 16 Public.aY) 16 < X) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (CrtIfma.k1 ++ ([.block (CrtIfma.arr52 p Public.aN oM),
      .block (CrtIfma.arr52 p aT oK1), .block (CrtIfma.arr52 p aXc oX),
      .block (CrtIfma.arr52 p Public.aY oY)] : List (Prog isa)))) s fun t =>
      Limbs t.mem (off B a) (D * p + oM) X ∧
      Limbs t.mem (off B a) (D * p + oK1) (2 ^ 32 * wv s.mem (off B o) (slot 16 Public.aY) 16 % X) ∧
      Limbs t.mem (off B a) (D * p + oX) (wv s.mem (off B o) (slot 16 aXc) 16) ∧
      Limbs t.mem (off B a) (D * p + oY) (wv s.mem (off B o) (slot 16 Public.aY) 16) ∧
      Frm B (shiftRanges o (k1Ranges 16) ++ [(a + D * p, D)]) s.mem t.mem ∧
      t.wr = s.wr ∧ t.gpr .rdi = off B o ∧ Keep mmRegs s t ∧ t.gpr .r12 = mask52 ∧
      Hdr t.mem (off B o) 16 mx ∧ word t.mem (off B o) (8 * sIfma) = off B a := by
  have hs := hc.scr
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hk1 : ∀ r ∈ k1Ranges 16, r.1 + r.2 ≤ slot 16 8 := by
    have := slot_le (w := 16) (show Public.aAcc < 8 by decide)
    have := slot_le (w := 16) (show Public.aTmp < 8 by decide)
    have := slot_le (w := 16) (show aT < 8 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [CrtIfma.sCtr, sFn] <;> omega
  refine wp_seqs_append (by simp [CrtIfma.k1, copyArr]) (by simp) (WP.mono (k1_ok hc.good (by decide)
    (by decide) hN hY) fun s₁ ⟨hT₁, f₁, hH₁, k₁⟩ => ?_)
  have hs₁ : Scr s₁ B Z := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = off B o := by rw [k₁.gpr (by decide)]; exact hc.rdi
  have hwv : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv s₁.mem (off B o) (slot 16 j) 16 = wv s.mem (off B o) (slot 16 j) 16 := fun j hj h1 h2 h3 => by
    have := slot_le (w := 16) hj
    exact f₁.wv_eq (k1Ranges_arr h1 h2 h3) (by omega)
  have hia₁ : word s₁.mem (off B o) (8 * sIfma) = off B a := by
    rw [f₁.word_eq (fun r hr => by
      have := slot_le (w := 16) (show Public.aAcc < 8 by decide)
      have := hdr_lt_slot 16 Public.aAcc (show sIfma < 32 by decide)
      have := hdr_lt_slot 16 Public.aTmp (show sIfma < 32 by decide)
      have := hdr_lt_slot 16 aT (show sIfma < 32 by decide)
      simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [CrtIfma.sCtr, sIfma, sFn] at * <;> omega)
      (by unfold sIfma sFn; omega)]
    exact hia
  have f₁' : Frm B (shiftRanges o (k1Ranges 16)) s.mem s₁.mem :=
    f₁.rebase (by omega) fun r hr => by have := hk1 r hr; omega
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (arrA_ok hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := Public.aN) (c := oM) (by decide)
    (by decide) (Frm.refl _ _ _) rfl rfl) fun t₁ ⟨lM, g₁, _, w₁, d₁, k₁', _⟩ => ?_)
  refine WP.seq (WP.mono (arrA_ok hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := aT) (c := oK1) (by decide) (by decide)
    g₁ w₁ d₁) fun t₂ ⟨lK, g₂, e₂, w₂, d₂, k₂, _⟩ => ?_)
  refine WP.seq (WP.mono (arrA_ok hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := aXc) (c := oX) (by decide) (by decide)
    g₂ w₂ d₂) fun t₃ ⟨lX, g₃, e₃, w₃, d₃, k₃, _⟩ => ?_)
  refine WP.mono (arrA_ok hs₁ hdi₁ hH₁ hia₁ hoa haZ hp (j := Public.aY) (c := oY) (by decide) (by decide)
    g₃ w₃ d₃) fun t ⟨lY, g₄, e₄, w₄, d₄, k₄, h12⟩ => ?_
  have sep : ∀ {c c' : Nat}, c + 160 ≤ c' ∨ c' + 160 ≤ c → ∀ r ∈ [(a + (D * p + c'), 160)],
      a + (D * p + c) + 160 ≤ r.1 ∨ r.1 + r.2 ≤ a + (D * p + c) := fun h r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega
  have : oM = 0 := rfl
  have : oK1 = 3360 := rfl
  have : oX = 352 := rfl
  have : oY = 192 := rfl
  rw [(hwv _ (by decide) (by decide) (by decide) (by decide)).trans hN] at lM
  rw [hT₁] at lK
  rw [hwv _ (by decide) (by decide) (by decide) (by decide)] at lX lY
  refine ⟨((lM.of_frm e₂ (sep (by decide)) (by omega)).of_frm e₃ (sep (by decide)) (by omega)).of_frm e₄
      (sep (by decide)) (by omega), (lK.of_frm e₃ (sep (by decide)) (by omega)).of_frm e₄ (sep (by decide))
      (by omega), lX.of_frm e₄ (sep (by decide)) (by omega), lY, f₁'.append g₄,
    w₄.trans k₁.2.2, d₄.trans hdi₁, ?_, h12, ?_, ?_⟩
  · exact (k₁.trans (((k₁'.trans k₂).trans k₃).trans k₄)).mono (by decide)
  · exact hH₁.of_below g₄ (fun r hr => by
      rw [List.mem_singleton.mp hr]; unfold hdrBytes; unfold slot hdrBytes at h8; simp only; omega)
      (by unfold hdrBytes; unfold slot hdrBytes at h8; omega)
  · rw [word_off, word_below_frm g₄ (L := a) (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega)
      (by unfold sIfma sFn; omega) (by omega), ← word_off]
    exact hia₁

/-! ## The region's tail -/

theorem byte_of_word0 {m : Mem} {F : Addr} {d k : Nat} (h : word m F d = 0) (hk : k < 8) :
    m (off F (d + k)) = 0 := by
  have e := VG.X86_64.byte_readW m (off F d) (w := 64) (k := k) (by omega)
  rw [show m.readW (off F d) 64 = word m F d from rfl, h, AmmSym.off_add] at e
  rw [← e]; simp

/-- `k0St` in a prime's workspace, the area at `off B a`. -/
theorem k0r_ok {u : State} {B : Addr} {Z o a p : Nat} {mx : BitVec 64} (hs : Scr u B Z)
    (hdi : u.gpr .rdi = off B o) (hH : Hdr u.mem (off B o) 16 mx)
    (hia : word u.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2) (h12 : u.gpr .r12 = mask52) :
    WP isa (.block (CrtIfma.k0St p)) u fun u' =>
      (∀ t < 4, word u'.mem (off B a) (D * p + oK0 + 8 * t) = mx &&& mask52) ∧
      Frm B [(a + D * p + oK0, 32)] u.mem u'.mem ∧ u'.gpr .r11 = off (off B a) (D * p) ∧
      Keep [.rax, .r11] u u' := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have : oK0 = 160 := rfl
  have hH' : ∀ i < 32, InRegions (u.rd ++ u.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot 16 8 hi; omega)
  refine WP.mono (AmmSym.k0St_ok (A := off B a) hdi hH' hia hH.hminv h12 (by omega) fun t ht => by
    rw [off_off, AmmSym.off_add]; exact hs.st (by omega)) fun u' ⟨hw, ho, r11, k, _⟩ => ⟨fun t ht => ?_, ?_, r11, k⟩
  · rw [Nat.add_assoc, ← word_off]; exact hw t ht
  · rw [off_off] at ho
    exact Frm.of_outside_off ho (by omega) (by omega)

/-- `eZero` with `r11` at region `p` of the area `off B a`. -/
theorem eZr_ok {u : State} {B : Addr} {Z a p : Nat} (hs : Scr u B Z) (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2)
    (h11 : u.gpr .r11 = off (off B a) (D * p)) :
    WP isa (.block CrtIfma.eZero) u fun u' =>
      (∀ i < 128, u'.mem (off (off B a) (D * p + oE + i)) = 0) ∧
      Frm B [(a + D * p + oE, 128)] u.mem u'.mem ∧ u'.gpr .rax = 0 ∧ Keep [.rax] u u' := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have : oE = 3232 := rfl
  refine WP.mono (AmmSym.eZero_ok h11 fun l hl => by
    rw [off_off, AmmSym.off_add]; exact hs.st (by omega)) fun u' ⟨hw, ho, ra, k, _⟩ => ⟨fun i hi => ?_, ?_, ra, k⟩
  · have e := byte_of_word0 (hw (i / 8) (by omega)) (show i % 8 < 8 from Nat.mod_lt _ (by decide))
    rw [show D * p + oE + i = D * p + (oE + 8 * (i / 8) + i % 8) by omega, ← off_off]
    exact e
  · rw [off_off] at ho
    exact Frm.of_outside_off ho (by omega) (by omega)

/-- `finOne` with `r11` at `q`'s region (`rax = 0`). -/
theorem finr_ok {u : State} {B : Addr} {Z a : Nat} (hs : Scr u B Z) (haZ : a + 2 * D + 8 ≤ Z)
    (h11 : u.gpr .r11 = off (off B a) (D * 1)) (ha : u.gpr .rax = 0) :
    WP isa (.block CrtIfma.finOne) u fun u' =>
      Limbs u'.mem (off B a) (D * 1 + oFin) 1 ∧ Frm B [(a + D * 1 + oFin, 160)] u.mem u'.mem ∧
      Keep [.rax] u u' := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have : oFin = 3552 := rfl
  refine WP.mono (AmmSym.finOne_ok h11 ha fun j hj => by
    have := off_lt160 hj
    rw [off_off, AmmSym.off_add]; exact hs.st (by omega)) fun u' ⟨hw, ho, k, _⟩ => ⟨fun j hj => ?_, ?_, k⟩
  · rw [Nat.add_assoc, ← word_off]; exact hw j hj
  · rw [off_off] at ho
    exact Frm.of_outside_off ho (by omega) (by omega)

/-- `eCopy` with `r11` at region `p` of the area `off B a`: the exponent's
bytes (`eb`, its pointer and length in `n`'s slots `sp` and `sl`) at the end
of the 128 at `oE`. -/
theorem eCr_ok {u : State} {B : Addr} {Z o a p sp sl L : Nat} {ep : Addr} {eb : List Byte} (hs : Scr u B Z)
    (hdi : u.gpr .rdi = off B o) (hlk : word u.mem (off B o) (8 * sLink) = B)
    (hoa : o + slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2)
    (hsp : sp < 32) (hsl : sl < 32) (hpv : word u.mem B (8 * sp) = ep)
    (hlv : word u.mem B (8 * sl) = BitVec.ofNat 64 L) (he : Src u B Z ep eb) (hL : eb.length = L)
    (hL1 : 1 ≤ L) (hL2 : L ≤ 128) (h11 : u.gpr .r11 = off (off B a) (D * p)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (CrtIfma.eCopy sp sl)) u fun u' =>
      (∀ i (h : i < L), u'.mem (off (off B a) (D * p + oE + (128 - L + i))) = eb[i]'(by omega)) ∧
      Frm B [(a + D * p + oE + (128 - L), L)] u.mem u'.mem ∧ Keep [.rax, .rcx, .rsi, .r11] u u' := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have : oE = 3232 := rfl
  have hC : ∀ i, off (off (off B a) (D * p)) (oE + 128 - L) + BitVec.ofNat 64 i =
      off B (a + D * p + oE + (128 - L) + i) := fun i => by
    rw [AmmSym.off_add, off_off, off_off]; congr 1; omega
  refine WP.mono (AmmSym.eCopy_ok (B := B) (W := off B o) hL hL1 hL2 hdi h11
    (by rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)) hlk
    (hs.ld (by unfold slot hdrBytes at h8; omega)) (hs.ld (by unfold slot hdrBytes at h8; omega)) hpv hlv
    (fun i hi => he.rd i (by omega)) (fun i hi => he.val i (by omega))
    (fun i hi => by rw [hC]; exact hs.st8 (by omega))
    (fun m m' ho i hi => by
      rw [off_off, off_off] at ho
      exact Frm.of_outside_off ho (by omega) (by omega) _ fun r hr => by
        rw [List.mem_singleton.mp hr]; have := he.out i (by omega); simp only; omega))
    fun u' ⟨hb, ho, k, _⟩ => ⟨fun i hi => ?_, ?_, k⟩
  · have e := hb i hi
    rw [hC] at e
    rw [off_off]
    rw [show a + (D * p + oE + (128 - L + i)) = a + D * p + oE + (128 - L) + i by omega]
    exact e
  · rw [off_off, off_off] at ho
    have := Frm.of_outside_off ho (by omega) (by omega)
    rwa [show a + (D * p + (oE + 128 - L)) + 0 = a + D * p + oE + (128 - L) by omega] at this

/-! ## The exponent's value -/

/-- The exponent padded with zero bytes at the top to 128. -/
def padE (eb : List Byte) : List Byte := List.replicate (128 - eb.length) 0 ++ eb

theorem os2ip_snoc (l : List Byte) (b : Byte) : Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem os2ip_zeros (l : List Byte) : ∀ k, Spec.Rsa.os2ip (List.replicate k 0 ++ l) = Spec.Rsa.os2ip l
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, ← os2ip_zeros l k]
    simp only [Spec.Rsa.os2ip, List.foldl_cons]
    rfl

/-- The bytes at `oE` read as `ev` reads them: big-endian. -/
theorem ev_os2ip (m : Mem) (F : Addr) (p : Nat) (bs : List Byte)
    (h : ∀ i (hi : i < bs.length), m (off F (D * p + oE + i)) = bs[i]) :
    ∀ n ≤ bs.length, AmmSym.ev m F p n = Spec.Rsa.os2ip (bs.take n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [AmmSym.ev, ev_os2ip m F p bs h n (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega),
      Option.toList_some, os2ip_snoc, h n (by omega), Nat.mul_comm]

theorem ev_padE {m : Mem} {F : Addr} {p : Nat} {eb : List Byte} (hL : eb.length ≤ 128)
    (h : ∀ i, i < 128 → m (off F (D * p + oE + i)) = (padE eb).getD i 0) :
    AmmSym.ev m F p 128 = Spec.Rsa.os2ip eb := by
  have hl : (padE eb).length = 128 := by simp only [padE, List.length_append, List.length_replicate]; omega
  have := ev_os2ip m F p (padE eb) (fun i hi => by
    rw [h i (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]) 128
    (by omega)
  rw [this, show (padE eb).take 128 = padE eb by rw [List.take_of_length_le (by omega)], padE, os2ip_zeros]

/-! ## The tail of a region -/

/-- What the tail's steps read: the prime's workspace `off B o` (16 words),
the area's base in it, `n`'s slots `sp` and `sl` (the exponent's pointer and
length), and the exponent. -/
structure TCtx (u : State) (B : Addr) (Z o a : Nat) (mx : BitVec 64) (sp sl : Nat) (ep : Addr)
    (eb : List Byte) : Prop where
  scr : Scr u B Z
  rdi : u.gpr .rdi = off B o
  hdr : Hdr u.mem (off B o) 16 mx
  ia : word u.mem (off B o) (8 * sIfma) = off B a
  lk : word u.mem (off B o) (8 * sLink) = B
  pv : word u.mem B (8 * sp) = ep
  lv : word u.mem B (8 * sl) = BitVec.ofNat 64 eb.length
  src : Src u B Z ep eb

theorem TCtx.of_frm {u u' : State} {B : Addr} {Z o a : Nat} {mx : BitVec 64} {sp sl : Nat} {ep : Addr}
    {eb : List Byte} (h : TCtx u B Z o a mx sp sl ep eb) {rs : List (Nat × Nat)} (hf : Frm B rs u.mem u'.mem)
    (hr : ∀ r ∈ rs, a ≤ r.1 ∧ r.1 + r.2 ≤ Z) (hoa : o + slot 16 8 + tabBytes 16 ≤ a) (haZ : a ≤ Z) (hsp : sp < 32)
    (hsl : sl < 32) (k : Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] u u') : TCtx u' B Z o a mx sp sl ep eb := by
  have hn := h.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hr' : ∀ r ∈ rs, a ≤ r.1 := fun r hr' => (hr r hr').1
  have hw : ∀ d, d + 8 ≤ a → word u'.mem B d = word u.mem B d := fun d hd =>
    word_below_frm hf hr' hd (by unfold slot hdrBytes at h8; omega)
  refine ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi,
    h.hdr.of_below hf (fun r hr'' => by have := hr' r hr''; unfold hdrBytes; unfold slot hdrBytes at h8; omega)
      (by unfold hdrBytes; unfold slot hdrBytes at h8; omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [word_off, hw _ (by unfold sIfma sFn; omega), ← word_off]; exact h.ia
  · rw [word_off, hw _ (by unfold sLink sFn; omega), ← word_off]; exact h.lk
  · rw [hw _ (by unfold slot hdrBytes at h8; omega)]; exact h.pv
  · rw [hw _ (by unfold slot hdrBytes at h8; omega)]; exact h.lv
  · exact h.src.congr (InScr.of_frm hf fun r hr'' => (hr r hr'').2) k.2.1 k.2.2

theorem padE_lo {eb : List Byte} {i : Nat} (hi : i < 128 - eb.length) : (padE eb).getD i 0 = 0 := by
  rw [padE, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_replicate]; omega),
    List.getElem?_replicate]
  simp only [hi, ↓reduceIte, Option.getD_some]

theorem padE_hi {eb : List Byte} {i : Nat} (h1 : 128 - eb.length ≤ i) (h2 : i < 128) (hL : eb.length ≤ 128) :
    (padE eb).getD i 0 = eb[i - (128 - eb.length)]'(by omega) := by
  rw [padE, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_replicate]; omega),
    List.length_replicate, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The ranges a region's tail writes. -/
def tailR (a p : Nat) : List (Nat × Nat) :=
  [(a + D * p + oFin, 160), (a + D * p + oK0, 32), (a + D * p + oE, 128)]

theorem tailR_bound {a p Z : Nat} (hp : p < 2) (haZ : a + 2 * D + 8 ≤ Z) :
    ∀ r ∈ tailR a p, a ≤ r.1 ∧ r.1 + r.2 ≤ Z := by
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  simp only [tailR, List.mem_cons, List.not_mem_nil, or_false, oFin, oK0, oE]
  rintro _ (rfl | rfl | rfl) <;> constructor <;> simp only <;> omega

/-- `p`'s tail: `R mod p` as the last multiplier, `k₀`, and the exponent. -/
theorem regionB0_ok {u : State} {B : Addr} {Z o a sp sl : Nat} {mx : BitVec 64} {ep : Addr} {eb : List Byte}
    (hc : TCtx u B Z o a mx sp sl ep eb) (hoa : o + slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * D + 8 ≤ Z)
    (hsp : sp < 32) (hsl : sl < 32) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 128) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (([.block (CrtIfma.arr52 0 Public.aY oFin), .block (CrtIfma.k0St 0),
      .block CrtIfma.eZero] : List (Prog isa)) ++ CrtIfma.eCopy sp sl)) u fun u' =>
      Limbs u'.mem (off B a) (D * 0 + oFin) (wv u.mem (off B o) (slot 16 Public.aY) 16) ∧
      (∀ t < 4, word u'.mem (off B a) (D * 0 + oK0 + 8 * t) = mx &&& mask52) ∧
      (∀ i, i < 128 → u'.mem (off (off B a) (D * 0 + oE + i)) = (padE eb).getD i 0) ∧
      Frm B (tailR a 0) u.mem u'.mem ∧ Keep mmRegs u u' := by
  have hn := hc.scr.nowrap
  have hD : D = 3712 := rfl
  have : oFin = 3552 := rfl
  have : oK0 = 160 := rfl
  have : oE = 3232 := rfl
  have hB := tailR_bound (a := a) (p := 0) (by decide) haZ
  refine wp_seqs_append (by simp) (by simp [CrtIfma.eCopy]) ?_
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (arr52r_ok hc.scr hc.rdi hc.hdr hc.ia hoa haZ (p := 0) (c := oFin) (j := Public.aY)
    (by decide) (by decide) (by decide)) fun u₁ ⟨lF, f₁, k₁, r12₁, _⟩ => ?_)
  have c₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoa (by omega)
    hsp hsl k₁
  refine WP.seq (WP.mono (k0r_ok c₁.scr c₁.rdi c₁.hdr c₁.ia hoa haZ (p := 0) (by decide) r12₁)
    fun u₂ ⟨hk, f₂, r11₂, k₂⟩ => ?_)
  have c₂ := c₁.of_frm f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoa (by omega)
    hsp hsl (k₂.mono (by simp))
  refine WP.mono (eZr_ok c₂.scr haZ (p := 0) (by decide) r11₂) fun u₃ ⟨hz, f₃, _, k₃⟩ => ?_
  have c₃ := c₂.of_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoa (by omega)
    hsp hsl (k₃.mono (by simp))
  have r11₃ : u₃.gpr .r11 = off (off B a) (D * 0) := by rw [k₃.gpr (by decide)]; exact r11₂
  refine WP.mono (eCr_ok c₃.scr c₃.rdi c₃.lk hoa haZ (p := 0) (by decide) hsp hsl c₃.pv c₃.lv c₃.src rfl hL1 hL2
    r11₃) fun u' ⟨hb, f₄, k₄⟩ => ?_
  refine ⟨((lF.of_frm f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega)).of_frm f₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega)).of_frm f₄
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega), fun t ht => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · rw [word_off, f₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega),
      f₃.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega), ← word_off]
    exact hk t ht
  · by_cases hlo : i < 128 - eb.length
    · rw [padE_lo hlo, off_off, byte_frm f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega)
        (by omega), ← off_off]
      exact hz i hi
    · rw [padE_hi (by omega) hi hL2, show D * 0 + oE + i = D * 0 + oE + (128 - eb.length + (i - (128 - eb.length)))
        by omega]
      exact hb _ (by omega)
  · refine (((f₁.append f₂).append f₃).append f₄).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((rfl | rfl) | rfl) | rfl
    · exact ⟨_, List.mem_cons_self .., by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega⟩
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)

/-- `q`'s tail: `k₀`, 1 as the last multiplier, and the exponent. -/
theorem regionB1_ok {u : State} {B : Addr} {Z o a sp sl : Nat} {mx : BitVec 64} {ep : Addr} {eb : List Byte}
    (hc : TCtx u B Z o a mx sp sl ep eb) (hoa : o + slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * D + 8 ≤ Z)
    (hsp : sp < 32) (hsl : sl < 32) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 128) (h12 : u.gpr .r12 = mask52) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (([.block (CrtIfma.k0St 1), .block CrtIfma.eZero, .block CrtIfma.finOne] :
      List (Prog isa)) ++ CrtIfma.eCopy sp sl)) u fun u' =>
      Limbs u'.mem (off B a) (D * 1 + oFin) 1 ∧
      (∀ t < 4, word u'.mem (off B a) (D * 1 + oK0 + 8 * t) = mx &&& mask52) ∧
      (∀ i, i < 128 → u'.mem (off (off B a) (D * 1 + oE + i)) = (padE eb).getD i 0) ∧
      Frm B (tailR a 1) u.mem u'.mem ∧ Keep mmRegs u u' := by
  have hn := hc.scr.nowrap
  have hD : D = 3712 := rfl
  have : oFin = 3552 := rfl
  have : oK0 = 160 := rfl
  have : oE = 3232 := rfl
  refine wp_seqs_append (by simp) (by simp [CrtIfma.eCopy]) ?_
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (k0r_ok hc.scr hc.rdi hc.hdr hc.ia hoa haZ (p := 1) (by decide) h12)
    fun u₁ ⟨hk, f₁, r11₁, k₁⟩ => ?_)
  have c₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoa (by omega)
    hsp hsl (k₁.mono (by simp))
  refine WP.seq (WP.mono (eZr_ok c₁.scr haZ (p := 1) (by decide) r11₁) fun u₂ ⟨hz, f₂, ra₂, k₂⟩ => ?_)
  have c₂ := c₁.of_frm f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoa (by omega)
    hsp hsl (k₂.mono (by simp))
  have r11₂ : u₂.gpr .r11 = off (off B a) (D * 1) := by rw [k₂.gpr (by decide)]; exact r11₁
  refine WP.mono (finr_ok c₂.scr haZ r11₂ ra₂) fun u₃ ⟨lF, f₃, k₃⟩ => ?_
  have c₃ := c₂.of_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoa (by omega)
    hsp hsl (k₃.mono (by simp))
  have r11₃ : u₃.gpr .r11 = off (off B a) (D * 1) := by rw [k₃.gpr (by decide)]; exact r11₂
  refine WP.mono (eCr_ok c₃.scr c₃.rdi c₃.lk hoa haZ (p := 1) (by decide) hsp hsl c₃.pv c₃.lv c₃.src rfl hL1 hL2
    r11₃) fun u' ⟨hb, f₄, k₄⟩ => ?_
  refine ⟨lF.of_frm f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega), fun t ht => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · rw [word_off, f₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega),
      f₃.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega),
      f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by omega), ← word_off]
    exact hk t ht
  · by_cases hlo : i < 128 - eb.length
    · rw [padE_lo hlo, off_off, byte_frm f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega)
        (by omega), byte_frm f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega)
        (by omega), ← off_off]
      exact hz i hi
    · rw [padE_hi (by omega) hi hL2, show D * 1 + oE + i = D * 1 + oE + (128 - eb.length + (i - (128 - eb.length)))
        by omega]
      exact hb _ (by omega)
  · refine (((f₁.append f₂).append f₃).append f₄).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((rfl | rfl) | rfl) | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega⟩
    · exact ⟨_, List.mem_cons_self .., by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega⟩
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)

/-! ## A region -/

/-- Region `p` of the area `F`: the modulus, `2¹⁰⁵⁶ mod X`, the base, `R`,
the last multiplier, `k₀`, and the padded exponent. -/
structure RegOut (m : Mem) (F : Addr) (p X K1 Xc Y Fin : Nat) (k0 : BitVec 64) (eb : List Byte) : Prop where
  n : Limbs m F (D * p + oM) X
  k1 : Limbs m F (D * p + oK1) K1
  x : Limbs m F (D * p + oX) Xc
  y : Limbs m F (D * p + oY) Y
  fin : Limbs m F (D * p + oFin) Fin
  k0 : ∀ t < 4, word m F (D * p + oK0 + 8 * t) = k0
  e : ∀ i, i < 128 → m (off F (D * p + oE + i)) = (padE eb).getD i 0

/-- A region after changes outside it. -/
theorem RegOut.of_frm {m m' : Mem} {B : Addr} {a p X K1 Xc Y Fin : Nat} {k0 : BitVec 64} {eb : List Byte}
    (h : RegOut m (off B a) p X K1 Xc Y Fin k0 eb) {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hd : ∀ r ∈ rs, a + D * p + D ≤ r.1 ∨ r.1 + r.2 ≤ a + D * p) (hz : a + D * p + D ≤ 2 ^ 64) :
    RegOut m' (off B a) p X K1 Xc Y Fin k0 eb := by
  have hD : D = 3712 := rfl
  have : oM = 0 := rfl
  have : oK1 = 3360 := rfl
  have : oX = 352 := rfl
  have : oY = 192 := rfl
  have : oFin = 3552 := rfl
  have : oK0 = 160 := rfl
  have : oE = 3232 := rfl
  have hl : ∀ {c}, c + 160 ≤ D → ∀ r ∈ rs, a + (D * p + c) + 160 ≤ r.1 ∨ r.1 + r.2 ≤ a + (D * p + c) :=
    fun hc r hr => by rcases hd r hr with h | h <;> omega
  exact ⟨h.n.of_frm hf (hl (by omega)) (by omega), h.k1.of_frm hf (hl (by omega)) (by omega),
    h.x.of_frm hf (hl (by omega)) (by omega), h.y.of_frm hf (hl (by omega)) (by omega),
    h.fin.of_frm hf (hl (by omega)) (by omega),
    fun t ht => by
      rw [word_off, hf.word_eq (fun r hr => by rcases hd r hr with h | h <;> omega) (by omega), ← word_off]
      exact h.k0 t ht,
    fun i hi => by
      rw [off_off, byte_frm hf (fun r hr => by rcases hd r hr with h | h <;> omega) (by omega), ← off_off]
      exact h.e i hi⟩

/-- The prime's workspace and `n`'s slots after `regionA`, for the tail. -/
theorem TCtx.of_regionA {s t : State} {B : Addr} {Z o w a p sp sl : Nat} {mx : BitVec 64} {ep : Addr}
    {eb : List Byte} (hc : SubCtx s B Z o w 16 mx) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2) (hsp : sp < 32) (hsl : sl < 32)
    (hpv : word s.mem B (8 * sp) = ep) (hlv : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (he : Src s B Z ep eb) (hf : Frm B (shiftRanges o (k1Ranges 16) ++ [(a + D * p, D)]) s.mem t.mem)
    (hwr : t.wr = s.wr) (hrd : t.rd = s.rd) (hdi : t.gpr .rdi = off B o) (hH : Hdr t.mem (off B o) 16 mx)
    (hia : word t.mem (off B o) (8 * sIfma) = off B a) : TCtx t B Z o a mx sp sl ep eb := by
  have hn := hc.scr.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hlo := hc.lo
  have hk1 : ∀ r ∈ k1Ranges 16, 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ slot 16 8 := by
    have := slot_le (w := 16) (show Public.aAcc < 8 by decide)
    have := slot_le (w := 16) (show Public.aTmp < 8 by decide)
    have := slot_le (w := 16) (show aT < 8 by decide)
    have := hdr_lt_slot 16 Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot 16 Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot 16 aT (show 31 < 32 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [CrtIfma.sCtr, sFn] <;> omega
  have hr : ∀ r ∈ shiftRanges o (k1Ranges 16) ++ [(a + D * p, D)], o + 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ Z := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      have := hk1 r' hr'; simp only; omega
    · rw [List.mem_singleton.mp hr]; simp only; omega
  have hw : ∀ d, d + 8 ≤ o + 8 * 30 → word t.mem B d = word s.mem B d := fun d hd =>
    word_below_frm hf (fun r h => (hr r h).1) hd (by omega)
  exact ⟨hc.scr.congr hwr, hdi, hH, hia,
    by rw [word_off, hw _ (by unfold sLink sFn; omega), ← word_off]; exact hc.link,
    by rw [hw _ (by omega)]; exact hpv,
    by rw [hw _ (by omega)]; exact hlv,
    he.congr (InScr.of_frm hf fun r h => (hr r h).2) hrd hwr⟩

theorem tailR_disj {a p : Nat} {c : Nat} (hc : c + 160 ≤ oK0 ∨ (oFin + 160 ≤ c ∧ c + 160 ≤ D) ∨
    (oK0 + 32 ≤ c ∧ c + 160 ≤ oE) ∨ (oE + 128 ≤ c ∧ c + 160 ≤ oFin)) :
    ∀ r ∈ tailR a p, a + (D * p + c) + 160 ≤ r.1 ∨ r.1 + r.2 ≤ a + (D * p + c) := by
  have : oFin = 3552 := rfl
  have : oK0 = 160 := rfl
  have : oE = 3232 := rfl
  have hD : D = 3712 := rfl
  simp only [tailR, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> simp only <;> omega

/-- `region p`: prime `p`'s region of the area at `off B a`, from its
workspace at `off B o` (16 words). -/
theorem region_ok {s : State} {B : Addr} {Z o w a p X sp sl : Nat} {mx : BitVec 64} {ep : Addr}
    {eb : List Byte} (hc : SubCtx s B Z o w 16 mx) (hia : word s.mem (off B o) (8 * sIfma) = off B a)
    (hoa : o + slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2)
    (hN : wv s.mem (off B o) (slot 16 Public.aN) 16 = X) (hY : wv s.mem (off B o) (slot 16 Public.aY) 16 < X)
    (hsp : sp < 32) (hsl : sl < 32) (hpv : word s.mem B (8 * sp) = ep)
    (hlv : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) (he : Src s B Z ep eb) (hL1 : 1 ≤ eb.length)
    (hL2 : eb.length ≤ 128) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (CrtIfma.region p sp sl)) s fun t =>
      RegOut t.mem (off B a) p X (2 ^ 32 * wv s.mem (off B o) (slot 16 Public.aY) 16 % X)
        (wv s.mem (off B o) (slot 16 aXc) 16) (wv s.mem (off B o) (slot 16 Public.aY) 16)
        (if p = 0 then wv s.mem (off B o) (slot 16 Public.aY) 16 else 1) (mx &&& mask52) eb ∧
      Frm B (shiftRanges o (k1Ranges 16) ++ [(a + D * p, D)]) s.mem t.mem ∧ t.wr = s.wr ∧
      t.gpr .rdi = off B o ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hD : D = 3712 := rfl
  have : oFin = 3552 := rfl
  have : oK0 = 160 := rfl
  have : oE = 3232 := rfl
  have : oM = 0 := rfl
  have : oK1 = 3360 := rfl
  have : oX = 352 := rfl
  have : oY = 192 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hwide : ∀ q, q < 2 → ∀ r ∈ tailR a q, ∃ r' ∈ shiftRanges o (k1Ranges 16) ++ [(a + D * q, D)],
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun q hq r hr => ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
    by
      have hDq : D * q ≤ 3712 := by rcases AmmSym.D_mul hq with h | h <;> omega
      simp only [tailR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega⟩
  have hY' : ∀ {t : State}, Frm B (shiftRanges o (k1Ranges 16) ++ [(a + D * p, D)]) s.mem t.mem →
      wv t.mem (off B o) (slot 16 Public.aY) 16 = wv s.mem (off B o) (slot 16 Public.aY) 16 := fun hf => by
    have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
    have lY := slot_le (w := 16) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]
    refine hf.wv_eq (fun r hr => ?_) (by omega)
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      rcases k1Ranges_arr (j := Public.aY) (by decide) (by decide) (by decide) r' hr' with h | h <;>
        simp only <;> omega
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
  · rw [show CrtIfma.region 0 sp sl = (CrtIfma.k1 ++ [.block (CrtIfma.arr52 0 Public.aN oM),
      .block (CrtIfma.arr52 0 aT oK1), .block (CrtIfma.arr52 0 aXc oX), .block (CrtIfma.arr52 0 Public.aY oY)]) ++
      ([.block (CrtIfma.arr52 0 Public.aY oFin), .block (CrtIfma.k0St 0), .block CrtIfma.eZero] ++
      CrtIfma.eCopy sp sl) from rfl]
    refine wp_seqs_append (by simp [CrtIfma.k1, copyArr]) (by simp) (WP.mono (regionA_ok hc hia hoa haZ hp hN hY)
      fun t ⟨lM, lK, lX, lY, fA, wA, dA, kA, _, hHA, iaA⟩ => ?_)
    refine WP.mono (regionB0_ok (TCtx.of_regionA hc hoa haZ hp hsp hsl hpv hlv he fA wA kA.2.1 dA hHA iaA) hoa haZ
      hsp hsl hL1 hL2) fun t' ⟨lF, hk, hE, fB, kB⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hk, hE⟩,
        fA.trans (fB.widen (hwide _ hp)), ?_, ?_, kA.trans kB |>.mono (by decide)⟩
    · exact lM.of_frm fB (tailR_disj (by omega)) (by omega)
    · exact lK.of_frm fB (tailR_disj (by omega)) (by omega)
    · exact lX.of_frm fB (tailR_disj (by omega)) (by omega)
    · exact lY.of_frm fB (tailR_disj (by omega)) (by omega)
    · rw [hY' fA] at lF
      rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0))]
      exact lF
    · rw [kB.2.2, wA]
    · rw [kB.gpr (by decide), dA]
  · rw [show CrtIfma.region 1 sp sl = (CrtIfma.k1 ++ [.block (CrtIfma.arr52 1 Public.aN oM),
      .block (CrtIfma.arr52 1 aT oK1), .block (CrtIfma.arr52 1 aXc oX), .block (CrtIfma.arr52 1 Public.aY oY)]) ++
      ([.block (CrtIfma.k0St 1), .block CrtIfma.eZero, .block CrtIfma.finOne] ++ CrtIfma.eCopy sp sl) from rfl]
    refine wp_seqs_append (by simp [CrtIfma.k1, copyArr]) (by simp) (WP.mono (regionA_ok hc hia hoa haZ hp hN hY)
      fun t ⟨lM, lK, lX, lY, fA, wA, dA, kA, r12, hHA, iaA⟩ => ?_)
    refine WP.mono (regionB1_ok (TCtx.of_regionA hc hoa haZ hp hsp hsl hpv hlv he fA wA kA.2.1 dA hHA iaA) hoa haZ
      hsp hsl hL1 hL2 r12) fun t' ⟨lF, hk, hE, fB, kB⟩ => ⟨⟨?_, ?_, ?_, ?_, lF, hk, hE⟩,
        fA.trans (fB.widen (hwide _ hp)), ?_, ?_, kA.trans kB |>.mono (by decide)⟩
    · exact lM.of_frm fB (tailR_disj (by omega)) (by omega)
    · exact lK.of_frm fB (tailR_disj (by omega)) (by omega)
    · exact lX.of_frm fB (tailR_disj (by omega)) (by omega)
    · exact lY.of_frm fB (tailR_disj (by omega)) (by omega)
    · rw [kB.2.2, wA]
    · rw [kB.gpr (by decide), dA]

end VG.Proof.Bignum.X86_64
