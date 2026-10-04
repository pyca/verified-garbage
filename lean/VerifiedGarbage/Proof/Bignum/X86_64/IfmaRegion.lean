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
