module
-- separate module: primes' body, a long proof, apart from its entry and return

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Prime
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.CopyBytes
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Read

/-! # An RSA private key's precomputed values on x86: the factors' values

`pqCheck_ok`: the mask at `accOff` all ones exactly when `p q = n` (as the
first half of `CrtRt.validate`, but with the product of `p`'s `⌈p_len / 4⌉`
words by `q`'s `⌈q_len / 4⌉`: `counts_lenW`, `CrtRt.productBy_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PrivPre (pqCheck primesBody check factor loadX lenW)
open VG.Proof.Bignum.X86.PublicRt (byteAddr_ptr)
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- `lenW i`: the bytes of the words of the length argument `i`. -/
theorem counts_lenW {len : Nat} {args : Nat → BitVec 32} {i : Nat} (hi : i < 18) (hL : (args i).toNat ≤ 1024) :
    Counts (lenW i) len args (((args i).toNat + 3) / 4) := by
  intro Ex base bytes s is Q r h kk
  simp only [lenW, List.cons_append, List.nil_append]
  refine wp_movS (h.arg hi) fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => wp_shr (by decide) fun s₃ u₃ _ => ?_
  refine wp_addS (src := .reg r) rfl fun s₄ u₄ _ => wp_addS (src := .reg r) rfl fun s₅ u₅ _ => ?_
  have w : ∀ {a b c : State}, Keeps [r] a b → Keeps [r] b c → Keeps [r] a c := fun h₁ h₂ => h₁.trans h₂
  refine kk s₅ (w (w (w (w u₁.keeps u₂.keeps) u₃.keeps) u₄.keeps) u₅.keeps)
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  apply BitVec.eq_of_toNat_eq
  have h3 : (args i + 3).toNat = (args i).toNat + 3 := by
    rw [BitVec.toNat_add, show (3 : BitVec 32).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, h3, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- A number of `n` words below `2^(32 k)`, `k ≤ n`, is its first `k`. -/
theorem val32_fit {m : Mem} {B : Addr} {d n k v : Nat} (hv : val32 m B d n = v) (hk : k ≤ n)
    (hlt : v < 2 ^ (32 * k)) : val32 m B d k = v := by
  have a := val32_append m B d k (n - k)
  rw [show k + (n - k) = n by omega_arith, hv] at a
  have hpos := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (n - k)) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at a; exact a.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) h; omega_arith

/-- A length's words hold a number of as many bytes. -/
theorem lt_words {v L : Nat} (h : v < 2 ^ (8 * L)) : v < 2 ^ (32 * ((L + 3) / 4)) :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega_arith))

theorem pqCheck_ok (h : In Ex base bytes len args s) {n p q : Nat}
    (hn : val32 s.mem base (lo len (.slot .wide 9)) (2 * cwc len .wide) = n)
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hq : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = q)
    (p1 : 1 ≤ (args 7).toNat) (pL : (args 7).toNat ≤ len) (q1 : 1 ≤ (args 9).toNat) (qL : (args 9).toNat ≤ len)
    (hpL : p < 2 ^ (8 * (args 7).toNat)) (hqL : q < 2 ^ (8 * (args 9).toNat)) :
    WP isa pqCheck s fun u =>
      Frame (frameR base (s.gpr .esp) (valR len)) s.mem u.mem ∧
      w32 u.mem base accOff = (cmask (decide (p * q = n))).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have nw := h.scratch.nowrap
  have f17 := h.slot_fit .wide (j := 17) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e10 : lo len (.slot .wide 10) = numBase + 10 * st len .wide := rfl
  have e11 : lo len (.slot .wide 11) = numBase + 11 * st len .wide := rfl
  have e14 : lo len (.slot .wide 14) = numBase + 14 * st len .wide := rfl
  have e18w : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have ao : accOff = 8 := rfl
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega_arith
  have ma : mulAOff = 2312 := rfl
  have po : prodOff = 256 := rfl
  have fitV := valR_fit h
  let cn := cwc len .wide
  unfold pqCheck
  -- `p` into the multiplicand, and `p q`.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 10) (d := mulA) (one_ok .wide) (by rw [cb1]; omega_arith)
    (by rw [cb1]; simp only [mulA, lo]; omega_arith) (by rw [cb1]; simp only [mulA, lo]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [mulA, lo, cb1, cw1] at O₁ V₁
  rw [show numBase + 10 * st len .wide = lo len (.slot .wide 10) from rfl, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  have k₁ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₁.mem base d k = val32 s.mem base d k :=
    fun hd hk => O₁.val32 (.inr (by omega_using [pf.2.1, hd])) (by omega_using [hk, h.bytes_lt])
  have lw := len_le_bc len
  have Np : ((args 7).toNat + 3) / 4 ≤ cn := by simp only [cn, cwc]; omega_arith
  have Nq : ((args 9).toNat + 3) / 4 ≤ cn := by simp only [cn, cwc]; omega_arith
  refine WP.seq (WP.mono (productBy_ok h₁ (counts_lenW (i := 9) (by decide) (by omega_arith))
    (fun h' he' kk => counts_lenW (i := 7) (by decide) (by omega_arith) .eax h' kk) (by omega_arith) (by omega_arith)
    Nq Np (b := .slot .wide 11) (by omega_arith) (by simp only [lo]; omega_arith))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [val32_fit V₁ Np (lt_words hpL), k₁ (d := lo len (.slot .wide 11)) (k := ((args 9).toNat + 3) / 4)
    (by omega_arith) (by omega_arith), val32_fit hq Nq (lt_words hqL)] at V₂
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (prodR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 s.mem base d k :=
    fun hd hk => (prodR_keep h₁ F₂ (sp₁ ▸ h₁.room) (by omega_arith) hk).trans (k₁ hd hk)
  -- `p q = n`.
  have pq : val32 u₂.mem base prodOff (2 * cn) = p * q := by
    have sp := val32_succ u₂.mem base prodOff (2 * cn)
    rw [V₂] at sp
    have hl := val32_lt u₂.mem base prodOff (2 * cn)
    have hpq : p * q < 2 ^ (32 * (2 * cn)) := by
      have := val32_lt s.mem base (lo len (.slot .wide 10)) cn
      have := val32_lt s.mem base (lo len (.slot .wide 11)) cn
      rw [hp] at *; rw [hq] at *
      rw [show 32 * (2 * cn) = 32 * cn + 32 * cn by omega_arith, Nat.pow_add]
      exact Nat.mul_lt_mul'' (by assumption) (by assumption)
    have : w32 u₂.mem base (prodOff + 4 * (2 * cn)) = 0 := by
      by_contra hne
      have : 2 ^ (32 * (2 * cn)) ≤ 2 ^ (32 * (2 * cn)) * w32 u₂.mem base (prodOff + 4 * (2 * cn)) :=
        Nat.le_mul_of_pos_right _ (by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero] at sp
    exact sp.symm
  refine WP.seq (WP.mono (equal_ok h₂ (a := prod) (b := .slot .wide 9) (two_ok .wide)
    (by rw [cb2]; simp only [prod, lo]; omega_using [pf.1, pf.2.1, pf.2.2]) (by rw [cb2]; omega_arith)) fun u₃ ⟨M₃, C₃, K₃⟩ => ?_)
  simp only [prod, lo, cw2] at C₃
  rw [show numBase + 9 * st len .wide = lo len (.slot .wide 9) from rfl, k₂ (d := lo len (.slot .wide 9)) (k := 2 * cwc len .wide) (by omega_arith) (by omega_arith), hn,
    show 2 * cwc len .wide = 2 * cn from rfl, pq] at C₃
  have h₃ := h₂.regs K₃ M₃
  -- The mask stored.
  refine wp_storeS (h₃.scratch.ea (d := accOff) (by omega_arith))
    (h₃.scratch.write (d := accOff) (n := 4) (by omega_arith)) fun u₄ m₄ => WP.block_nil ?_
  have O₄ : Outside base accOff 4 u₃.mem u₄.mem := by rw [m₄.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  have A₄ : w32 u₄.mem base accOff = (cmask (decide (p * q = n))).toNat := by
    rw [m₄.mem, w32_write_self, C₃]
  refine ⟨?_, A₄, (((K₁.mono (by decide)).trans K₂).trans K₃).trans ((m₄.keeps []).mono (by decide))⟩
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have F₁ : Frame (frameR base (s.gpr .esp) (valR len)) s.mem u₁.mem :=
    frameR_of_outside O₁ (by omega_arith) (by simp)
  have F₂' : Frame (frameR base (s.gpr .esp) (valR len)) u₁.mem u₂.mem :=
    frameR_mono F₂ fun p hp => by
      simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
  have F₄ : Frame (frameR base (s.gpr .esp) (valR len)) u₂.mem u₄.mem := by
    rw [← M₃]; exact frameR_of_outside O₄ (by omega_arith) (by simp)
  exact (F₁.trans F₂').trans F₄

/-- A factor's value is below `2^(8 L)` for its length `L`. -/
theorem component_lt (m : Mem) (args : Nat → BitVec 32) (i : Nat) :
    componentValue m args i < 2 ^ (8 * (args (i + 1)).toNat) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)
  rwa [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] at this

/-- `x` as the input holds it: its `len` bytes, little-endian. -/
abbrev xIn (m : Mem) (args : Nat → BitVec 32) (len : Nat) : Nat := (m.read (byteAddr (args 4)) len).toNat

/-- `loadX`: the input's `len` bytes into the zeroed wide slot 18. -/
theorem loadX_ok (h : RIn base bytes len args s) :
    WP isa loadX s fun u =>
      Outside base (lo len (.slot .wide 18)) (2 * bc len .wide) s.mem u.mem ∧
      xv u.mem base len = xIn s.mem args len ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have W18 := h.wide_fit (j := 18) (by decide)
  have N := two_ok .wide
  have ce := cb_eq (len := len) N
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have bww := bc_eq_cwc len .wide
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by simp [cw, cwc, cb, two]; omega_arith
  have lw := len_le_bc len
  have pos : 0 < len := by have := h.lower'; omega_arith
  have x := h.extra
  have m4 : (4 : Nat) ∈ componentArguments := by simp [componentArguments]
  have hlen : (args 5).toNat = len := by rw [x.inLen, BitVec.toNat_ofNat]; have := h.upper'; omega_arith
  have fit : (args 4).toNat + len ≤ 2 ^ 32 := by have := x.fits 4 m4; rwa [hlen] at this
  have rd : InRegions (s.rd ++ s.wr) (byteAddr (args 4)) len := by have := x.readable 4 m4; rwa [hlen] at this
  have apart : Region.Disjoint ⟨byteAddr (args 4), len⟩ ⟨base, bytes⟩ := by
    have := x.apart 4 m4; rwa [hlen] at this
  have hx : lo len (.slot .wide 18) + cb len (two .wide) ≤ bytes := by rw [cb2]; omega_arith
  unfold loadX
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, Z, K⟩ => ?_)
  rw [cb2] at O
  rw [cw2] at Z
  have Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega_arith)
  have hu := h.keep K (by decide) (by decide) Ou
  refine WP.seq (ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_arith)
    fun v Kv mv pv => ?_)
  have hv := hu.regs Kv mv
  refine wp_movS (hv.arg (by decide : 4 < 18)) fun v₁ u₁ _ => ?_
  have hv₁ := hv.regs u₁.keeps u₁.mem
  refine wp_movS (hv₁.arg (by decide : 5 < 18)) fun v₂ u₂ _ => WP.block_nil ?_
  have K₂ : Keeps [.ecx, .esi] v v₂ := (u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))
  have m₂ : v₂.mem = u.mem := by rw [u₂.mem, u₁.mem, mv]
  have ecx₂ : v₂.gpr .ecx = BitVec.ofNat 32 len := by
    rw [u₂.gpr, x.inLen]
  have esi₂ : v₂.gpr .esi = args 4 := by rw [u₂.other _ (by decide), u₁.gpr]
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₂ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₂.mono (by decide)))
  have hv₂ : RIn base bytes len args v₂ := hv.regs K₂ (by rw [m₂, mv])
  let dst := v₂.gpr .ebx
  have ebx₂ : dst = v.gpr .ebx := by
    show v₂.gpr .ebx = _; rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have pv₂ : PtrAt v₂ base .ebx (lo len (.slot .wide 18)) := by
    show (v₂.gpr .ebx).toNat = _; rw [show v₂.gpr .ebx = v.gpr .ebx from ebx₂]; exact pv
  have dstAddr : byteAddr dst = off base (lo len (.slot .wide 18)) := byteAddr_ptr pv₂ (by omega_arith)
  have dstNat : dst.toNat = base.toNat + lo len (.slot .wide 18) := by
    show (v₂.gpr .ebx).toNat = _; rw [pv₂, Nat.mod_eq_of_lt (by omega_arith)]
  have vw : InRegions v₂.wr (byteAddr dst) len := by
    rw [dstAddr]; exact hv₂.scratch.write (by omega_arith)
  have vr : InRegions (v₂.rd ++ v₂.wr) (byteAddr (args 4)) len := by rw [keep.2.1, keep.2.2]; exact rd
  have hsub : Region.Sub ⟨off base (lo len (.slot .wide 18)), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len (.slot .wide 18)) (n := len) (e := 0) (k := bytes) (Nat.zero_le _)
      (by omega_arith)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have hd : Region.Disjoint ⟨byteAddr (args 4), len⟩ ⟨byteAddr dst, len⟩ := by
    rw [dstAddr]; exact apart.sub_right hsub
  have ctx := copyCtx_of_regions v₂ (args 4) dst (by omega_arith) fit (by omega_arith) vr vw hd
  refine WP.mono (copyBytes_ok v₂ ctx pos esi₂ rfl ecx₂) fun t I => ?_
  have Ot : Outside base (lo len (.slot .wide 18)) (2 * bc len .wide) v₂.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs base a = lo len (.slot .wide 18) + k := by
      rw [he, byteAddr_add (by omega_arith), dstAddr]
      exact ofs_off base (by omega_arith)
    omega_arith
  have padding : ∀ k, len ≤ k → k < 4 * (2 * cwc len .wide) →
      t.mem (off base (lo len (.slot .wide 18)) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₂]
    · exact byte_zero_of_val32 Z (by omega_arith)
    · intro i hi he
      rw [byteAddr_add (by omega_arith), dstAddr] at he
      have e := congrArg (fun a => (a - off base (lo len (.slot .wide 18))).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega_arith : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega_arith : i < 2 ^ 64)] at e
      omega_arith
  refine ⟨(by rw [m₂]; exact O : Outside _ _ _ s.mem v₂.mem).trans Ot, ?_, keep.trans (I.rest.mono (by decide))⟩
  have value := I.read fit (by omega_arith : dst.toNat + len ≤ 2 ^ 32) (d := 0) (width := len) (by omega_arith)
  simp only [BitVec.add_zero] at value
  rw [dstAddr] at value
  have src : v₂.mem.read (byteAddr (args 4)) len = s.mem.read (byteAddr (args 4)) len := by
    apply Mem.read_congr
    intro i hi
    have H := apart (byteAddr (args 4) + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_arith) (by omega_arith))
    change ¬ (ofs base (byteAddr (args 4) + BitVec.ofNat 64 i) + 1 ≤ bytes) at H
    rw [m₂]; exact Ou _ (.inr (by omega_arith))
  simp only [xv, xIn]
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off base (lo len (.slot .wide 18))) (n := 2 * cwc len .wide)
    (by omega_arith : len ≤ 4 * (2 * cwc len .wide)) padding
  rw [← read_eq_val32] at ext
  rw [← src, ← value]
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext

/-- The ranges of the working space the body changes. -/
abbrev bodyR (len : Nat) : List (Nat × Nat) :=
  (lo len (.slot .wide 18), 2 * bc len .wide) :: (lo len (.slot .wide 9), 7 * st len .wide) ::
    (valR len ++ factorR len 16 ++ factorR len 17)

/-- The body but its load of `x`, from `x` in the wide slot 18: `n`, `p` and
`q` loaded, the mask of `p q = n`, then each factor's `R² mod p` into the
wide slots 16 (`p`) and 17 (`q`) where `x ≡ 2^(128 w)`, and the mask's low
bit in `eax`. -/
theorem bodyRest_ok (h : RIn base bytes len args s) (hX : xv s.mem base len < 2 ^ (8 * bc len .wide)) :
    WP isa (.seq check <| .seq (factor 10 7 16) <| .seq (factor 11 9 17)
        (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)])) s fun u =>
      Frame (frameR base (s.gpr .esp) ((lo len (.slot .wide 9), 7 * st len .wide) ::
        (valR len ++ factorR len 16 ++ factorR len 17))) s.mem u.mem ∧
      (xv s.mem base len % safeM (componentValue s.mem args 6) =
          2 ^ fixB len % safeM (componentValue s.mem args 6) →
        val32 u.mem base (lo len (.slot .wide 16)) (2 * Spec.Rsa.primeWords (args 7).toNat) =
          2 ^ r2Exp (args 7).toNat % safeM (componentValue s.mem args 6)) ∧
      (xv s.mem base len % safeM (componentValue s.mem args 8) =
          2 ^ fixB len % safeM (componentValue s.mem args 8) →
        val32 u.mem base (lo len (.slot .wide 17)) (2 * Spec.Rsa.primeWords (args 9).toNat) =
          2 ^ r2Exp (args 9).toNat % safeM (componentValue s.mem args 8)) ∧
      u.gpr .eax = BitVec.ofNat 32 (decide (componentValue s.mem args 6 * componentValue s.mem args 8 =
        componentValue s.mem args 2)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have pf := h.prod_fit
  have hup := h.upper'
  have f18 := h.slot_fit .wide (j := 18) (by decide)
  have bw := bc_eq_cwc len .wide
  have bwh := bc_le_wide len .half
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  have nb : numBase = 3336 := rfl
  have p7 : 0 < (args 7).toNat := h.extra.positive 6 (by simp [componentArguments])
  have b7 : (args 7).toNat ≤ len := h.extra.bounded 6 (by simp [componentArguments])
  have p9 : 0 < (args 9).toNat := h.extra.positive 8 (by simp [componentArguments])
  have b9 : (args 9).toNat ≤ len := h.extra.bounded 8 (by simp [componentArguments])
  have gw := bc_ge h.lower' .wide
  have pw7 : 2 * Spec.Rsa.primeWords (args 7).toNat ≤ cwc len .wide := by
    have := len_le_bc len; have := bc_dvd len .wide
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords, cwc]; omega_arith
  have pw9 : 2 * Spec.Rsa.primeWords (args 9).toNat ≤ cwc len .wide := by
    have := len_le_bc len; have := bc_dvd len .wide
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords, cwc]; omega_arith
  have e9 := el 9
  have e10 := el 10
  have e11 := el 11
  have e16 := el 16
  have e17 := el 17
  have e18 := el 18
  -- A frame of `factorR len o` keeps a number from the wide slot 9 on that misses the slot `o`.
  have keepR : ∀ {o : Nat} {sp : BitVec 32} {v : State} {m m' : Mem}, 16 ≤ o → o ≤ 17 →
      RIn base bytes len args v → CallRoom sp base bytes → Frame (frameR base sp (factorR len o)) m m' →
      ∀ {d k : Nat}, lo len (.slot .wide 9) ≤ d → d + 4 * k ≤ bytes →
        (d + 4 * k ≤ lo len (.slot .wide o) ∨ lo len (.slot .wide o) + bc len .wide ≤ d) →
        val32 m' base d k = val32 m base d k := by
    intro o sp v m m' ho16 ho hv R F d k hd hk hdo
    refine frameR_val32 F R nw hk (fun q hq => ?_) (fun q hq => (factorR_props hv ho16 ho q hq).1)
    rcases (factorR_props hv ho16 ho q hq).2.2 with hb | ⟨e, hl⟩
    · exact .inr (Nat.le_trans hb hd)
    · rw [e]; rcases hdo with hdo | hdo
      · exact .inl hdo
      · exact .inr (by omega_using [hl, hdo])
  have keepA : ∀ {o : Nat} {sp : BitVec 32} {v : State} {m m' : Mem}, 16 ≤ o → o ≤ 17 →
      RIn base bytes len args v → CallRoom sp base bytes → Frame (frameR base sp (factorR len o)) m m' →
      w32 m' base accOff = w32 m base accOff := by
    intro o sp v m m' ho16 ho hv R F
    rw [← w32_val32_one, ← w32_val32_one]
    exact frameR_val32 F R nw (by simp only [accOff]; omega_arith)
      (fun q hq => by have := (factorR_props hv ho16 ho q hq).2.1; simpa using this)
      (fun q hq => (factorR_props hv ho16 ho q hq).1)
  unfold check
  -- `n`, `p` and `q` (and the rest of the components).
  refine WP.seq (WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, n₁, _, p₁, q₁, _, _, _, K₁⟩ => ?_))
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- `p q = n`.
  refine WP.mono (pqCheck_ok h₁ n₁ p₁ q₁ p7 b7 p9 b9 (component_lt _ _ 6) (component_lt _ _ 8))
    fun u₂ ⟨F₂, A₂, K₂⟩ => ?_
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (valR_fit h₁)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 u₁.mem base d k :=
    fun hd hk => valR_keep h₁ F₂ h₁.room hd hk
  have X₂ : xv u₂.mem base len = xv s.mem base len := by
    simp only [xv]; rw [k₂ (by omega_arith) (by omega_arith), O₁.val32 (.inr (by omega_arith)) (by omega_arith)]
  -- The factor `p`.
  refine WP.seq (WP.mono (factor_ok h₂ (f := 10) (i := 7) (o := 16) (p := componentValue s.mem args 6) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [k₂ (by omega_arith) (by omega_arith), p₁])
    (by omega_using [p7]) b7 (component_lt s.mem args 6) (by rw [X₂]; exact hX))
    fun u₄ ⟨F₄, V₄, K₄⟩ => ?_)
  have h₄ := h₂.keepF K₄ (by decide) (by decide) F₄ (fun q hq => (factorR_props h₂ (by decide) (by decide) q hq).1)
  have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₂
  rw [sp₂] at F₄
  have X₄ : xv u₄.mem base len = xv s.mem base len := by
    simp only [xv]
    rw [keepR (o := 16) (by decide) (by decide) h₂ h.room F₄ (by omega_arith) (by omega_arith) (.inr (by omega_arith))]
    exact X₂
  -- The factor `q`.
  have q₄ : val32 u₄.mem base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue s.mem args 8 := by
    rw [keepR (o := 16) (by decide) (by decide) h₂ h.room F₄ (by omega_arith) (by omega_arith) (.inl (by omega_arith)),
      k₂ (by omega_arith) (by omega_arith), q₁]
  refine WP.seq (WP.mono (factor_ok h₄ (f := 11) (i := 9) (o := 17) (p := componentValue s.mem args 8) (by decide)
    (by decide) (by decide) (by decide) (by decide) q₄ (by omega_using [p9]) b9 (component_lt s.mem args 8) (by rw [X₄]; exact hX))
    fun u₆ ⟨F₆, V₆, K₆⟩ => ?_)
  rw [sp₄] at F₆
  have h₆ := h₄.keepF K₆ (by decide) (by decide) (by rw [sp₄]; exact F₆)
    (fun q hq => (factorR_props h₄ (by decide) (by decide) q hq).1)
  -- The result.
  have acc : w32 u₆.mem base accOff = (cmask (decide (componentValue s.mem args 6 * componentValue s.mem args 8 =
      componentValue s.mem args 2))).toNat := by
    rw [keepA (o := 17) (by decide) (by decide) h₄ h.room F₆, keepA (o := 16) (by decide) (by decide) h₂ h.room F₄,
      A₂]
  refine wp_movS (readSrc_sc h₆.scratch (d := accOff) (by simp only [accOff]; omega_arith)) fun u₇ a₇ _ => ?_
  refine VG.X86.Wp.wp_andi fun u a => WP.block_nil ?_
  have mu : u.mem = u₆.mem := by rw [a.mem, a₇.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₁] at F₂
    rw [mu]
    have mem : ∀ {q : Nat × Nat}, q ∈ valR len ++ factorR len 16 ++ factorR len 17 →
        q ∈ (lo len (.slot .wide 9), 7 * st len .wide) :: (valR len ++ factorR len 16 ++ factorR len 17) :=
      fun hq => List.mem_cons_of_mem _ hq
    exact (((frameR_of_outside O₁ (by omega_arith) (List.mem_cons_self ..)).trans
      (frameR_mono F₂ fun q hq => mem (List.mem_append_left _ (List.mem_append_left _ hq)))).trans
      (frameR_mono F₄ fun q hq => mem (List.mem_append_left _ (List.mem_append_right _ hq)))).trans
      (frameR_mono F₆ fun q hq => mem (List.mem_append_right _ hq))
  · intro e
    rw [mu, keepR (o := 17) (by decide) (by decide) h₄ h.room F₆ (by omega_arith) (by omega_arith)
      (.inl (by omega_arith))]
    exact V₄ (by rw [X₂]; exact e)
  · intro e; rw [mu]; exact V₆ (by rw [X₄]; exact e)
  · rw [a.gpr, a₇.gpr]
    have e : u₆.mem.readW (off base accOff) 32 = cmask (decide (componentValue s.mem args 6 *
        componentValue s.mem args 8 = componentValue s.mem args 2)) := BitVec.eq_of_toNat_eq acc
    rw [e]
    cases decide (componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2) <;> rfl
  · exact (((((K₁.mono (by decide)).trans K₂).trans K₄).trans K₆).trans (a₇.keeps.mono (by decide))).trans
      (a.keeps.mono (by decide))

/-- The body of the factors' values, after the entry: `x` from the input
(`loadX`), then `bodyRest_ok`. -/
theorem primesBody_ok (h : RIn base bytes len args s) :
    WP isa primesBody s fun u =>
      Frame (frameR base (s.gpr .esp) (bodyR len)) s.mem u.mem ∧
      (xIn s.mem args len % safeM (componentValue s.mem args 6) =
          2 ^ fixB len % safeM (componentValue s.mem args 6) →
        val32 u.mem base (lo len (.slot .wide 16)) (2 * Spec.Rsa.primeWords (args 7).toNat) =
          2 ^ r2Exp (args 7).toNat % safeM (componentValue s.mem args 6)) ∧
      (xIn s.mem args len % safeM (componentValue s.mem args 8) =
          2 ^ fixB len % safeM (componentValue s.mem args 8) →
        val32 u.mem base (lo len (.slot .wide 17)) (2 * Spec.Rsa.primeWords (args 9).toNat) =
          2 ^ r2Exp (args 9).toNat % safeM (componentValue s.mem args 8)) ∧
      u.gpr .eax = BitVec.ofNat 32 (decide (componentValue s.mem args 6 * componentValue s.mem args 8 =
        componentValue s.mem args 2)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have W18 := h.wide_fit (j := 18) (by decide)
  have lw := len_le_bc len
  unfold primesBody
  refine WP.seq (WP.mono (loadX_ok h) fun u₀ ⟨O₀, X₀, K₀⟩ => ?_)
  have Ou : Outside base 0 bytes s.mem u₀.mem := O₀.mono (Nat.zero_le _) (by omega_arith)
  have h₀ := h.keep K₀ (by decide) (by decide) Ou
  have sp₀ : u₀.gpr .esp = s.gpr .esp := K₀.1 _ (by decide)
  have cv : ∀ i ∈ componentArguments, componentValue u₀.mem args i = componentValue s.mem args i := by
    intro i hi
    simp only [componentValue]
    rw [VG.Proof.Bignum.scratch_bytes Ou (by have := (args (i + 1)).isLt; omega_arith) (h.extra.apart i hi)]
  have hX : xv u₀.mem base len < 2 ^ (8 * bc len .wide) := by
    rw [X₀]
    exact Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine WP.mono (bodyRest_ok h₀ hX) fun u ⟨F, V16, V17, eax, K⟩ => ?_
  rw [cv 2 (by decide), cv 6 (by decide), cv 8 (by decide)] at eax
  rw [cv 6 (by decide), X₀] at V16
  rw [cv 8 (by decide), X₀] at V17
  rw [sp₀] at F
  refine ⟨(frameR_of_outside O₀ (by omega_arith) (List.mem_cons_self ..)).trans
    (frameR_mono F fun q hq => List.mem_cons_of_mem _ hq), V16, V17, eax, K₀.trans K⟩

/-- `bodyR`'s ranges fit the working space and miss bytes 32 to 48 of it,
where the entry saved the callee-saved registers. -/
theorem bodyR_props (h : RIn base bytes len args s) :
    ∀ q ∈ bodyR len, q.1 + q.2 ≤ bytes ∧ (48 ≤ q.1 ∨ q.1 + q.2 ≤ 32) := by
  have pf := h.prod_fit
  have f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  have e9 := el 9
  have e18 := el 18
  have nb : numBase = 3336 := rfl
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by dsimp only; omega_arith, .inl (by dsimp only; omega_arith)⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by dsimp only; omega_arith, .inl (by dsimp only; omega_arith)⟩
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · refine ⟨valR_fit h q hq, ?_⟩
      simp only [valR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;>
        simp only [accOff, multOff, prodOff, mulAOff] at * <;> omega_using []
    · exact ⟨(factorR_props h (o := 16) (by decide) (by decide) q hq).1, factorR_saved q hq⟩
  · exact ⟨(factorR_props h (o := 17) (by decide) (by decide) q hq).1, factorR_saved q hq⟩

end

end VG.Proof.Bignum.X86.PrivPre
