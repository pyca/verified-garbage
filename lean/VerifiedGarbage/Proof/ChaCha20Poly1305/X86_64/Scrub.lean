module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Fn
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.By
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Leaves
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Registration

/-!
# ChaCha20-Poly1305 on x86-64: returning without secret residue

Every instance keeps its working space, `ctx`, in a frame that wipes its
first 672 bytes after the code (`framed`, `OpenTo.scratched`), with stores
aligned to 16 bytes. The clearing after the function wipes every granule of
the stack it uses but those wholly in `ctx` (or, where the instance chooses by
the length between codes with `ctx` at different places, in both). Each run
leaves `ctx` as `ctxL` says: zero in the bytes the frame wipes; in the
keystream area, `ctx[672, 1696)`, zero in the first `ksZ` bytes, which the code
zeroes and past which it writes none (`KsLeftZ`: `seal_correctK` and
`shared_correctK`, or the stitched code's `sealStitched_correctK` and
`stitchedShared_correctK`), and elsewhere as it found it. That is a function
of the stack pointer and the length alone, which two runs with the same public
data agree on, so two runs leave the same bytes there (`resOk_of_leaves`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Scrub

open VG VG.X86_64 VG.X86_64.Scrub VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Shared
open VG.Proof.ChaCha20.X86_64 (XorImpl)
open VG.Impl.Scrub.X86_64 (chunks)

/-- The keystream area of a context at `C`. -/
abbrev ksR (C : Addr) : Region := ⟨C + BitVec.ofNat 64 672, 1024⟩

/-- What `KsLeftZ` says is left at `x` in the keystream area of a context at
`C`, for data of `Lx` bytes: zero in its first `ksZ v Lx` bytes, else what was
there (`none`). -/
def ksL (v : XorImpl) (C : Addr) (Lx : Nat) (x : Addr) : Option (BitVec 8) :=
  if (x - (C + BitVec.ofNat 64 672)).toNat < ksZ v Lx then some 0 else none

theorem ksLeftAt_leaves {v : XorImpl} {C : Addr} {Lx : Nat} {m₀ m : Mem} (h : KsLeftZ v C Lx m₀ m)
    {x : Addr} (hx : (ksR C).Contains x 1) : m x = (ksL v C Lx x).getD (m₀ x) := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 1024 ∧ x = off C (672 + k) := by
    refine ⟨(x - (C + BitVec.ofNat 64 672)).toNat, by simp only [Region.Contains] at hx; omega_using [hx], ?_⟩
    rw [off_eq, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm,
      BitVec.sub_add_cancel]
  have e : (off C (672 + k) - (C + BitVec.ofNat 64 672)).toNat = k := by
    rw [off_eq, BitVec.ofNat_add, ← BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hk])]
  simp only [ksL, e]
  rw [h k hk]
  split <;> rfl

/-- A context at `C`: its first 672 bytes, which its frame wipes, then the
keystream area. -/
abbrev ctxR (C : Addr) : Region := ⟨C, 1696⟩

/-- What is left in a context at `C`: zeros in the 672 bytes its frame wipes,
and the keystream area as `ksL` says. -/
def ctxL (v : XorImpl) (C : Addr) (Lx : Nat) (x : Addr) : Option (BitVec 8) :=
  if (x - C).toNat < 672 then some 0 else ksL v C Lx x

theorem ctx_leaves {v : XorImpl} {C : Addr} {Lx : Nat} {m₀ m : Mem}
    (hz : ∀ x, (⟨C, 16 * 42⟩ : Region).Contains x 1 → m x = 0)
    (hk : ∀ x, (ksR C).Contains x 1 → m x = (ksL v C Lx x).getD (m₀ x))
    {x : Addr} (hx : (ctxR C).Contains x 1) : m x = (ctxL v C Lx x).getD (m₀ x) := by
  simp only [ctxL]
  by_cases h : (x - C).toNat < 672
  · rw [VG.X86_64.Scrub.ite_t h]
    exact hz x (by simp only [Region.Contains]; omega_using [h])
  · rw [VG.X86_64.Scrub.ite_f h]
    refine hk x ?_
    simp only [Region.Contains] at hx ⊢
    have := (Offset.lt_iff x C (d := 672) (n := 1024) (by decide)).2 ⟨by omega_using [h], by omega_using [hx]⟩
    omega_using [this]

/-- The keystream area of a context lies above the bytes its frame wipes. -/
theorem ks_not_wiped {C y : Addr} (hy : (ksR C).Contains y 1) : ¬ (⟨C, 16 * 42⟩ : Region).Contains y 1 :=
  fun hc => by
    have := (Offset.lt_iff y C (d := 672) (n := 1024) (by decide)).1 (by
      simp only [Region.Contains] at hy; omega_using [hy])
    simp only [Region.Contains] at hc
    omega_using [this, hc]

/-- What is left in a context reads the memory it started from only in the
keystream area. -/
theorem ctxL_congr {v : XorImpl} {C : Addr} {Lx : Nat} {m₁ m₂ : Mem} {x : Addr}
    (h : ¬ (x - C).toNat < 672 → m₁ x = m₂ x) : (ctxL v C Lx x).getD (m₁ x) = (ctxL v C Lx x).getD (m₂ x) := by
  simp only [ctxL]
  by_cases hc : (x - C).toNat < 672
  · rw [VG.X86_64.Scrub.ite_t hc]; rfl
  · rw [VG.X86_64.Scrub.ite_f hc, h hc]

/-- What code that chooses by the length (`r9`) between `a` and `c`, after a
comparison that writes only flags (`FlagsOnly`), leaves in `R`: what the code
it chooses leaves. -/
theorem choose_leaves {b : List Instr} {p : Addr → Bool} {a c : Prog isa} {P : State → Prop}
    {R : State → Region} {La Lc : State → Addr → Option (BitVec 8)}
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ Stitch.FlagsOnly s u)
    (hP : ∀ s u, Stitch.FlagsOnly s u → P s → P u)
    (hR : ∀ s u, Stitch.FlagsOnly s u → R u = R s)
    (hLa : ∀ s u, Stitch.FlagsOnly s u → La u = La s) (hLc : ∀ s u, Stitch.FlagsOnly s u → Lc u = Lc s)
    (ha : ∀ s t u, P s → Exec isa a s t u → ∀ x, (R s).Contains x 1 → u.mem x = (La s x).getD (s.mem x))
    (hc : ∀ s t u, P s → Exec isa c s t u → ∀ x, (R s).Contains x 1 → u.mem x = (Lc s x).getD (s.mem x))
    {s : State} {t : List Leak} {u : State} (hs : P s)
    (he : Exec isa (.seq (.block b) (Code.iteCold .b a c)) s t u) (x : Addr) (hx : (R s).Contains x 1) :
    u.mem x = ((if p (s.gpr .r9) then La s else Lc s) x).getD (s.mem x) := by
  obtain ⟨t₁, s₁, e₁, hq, hf⟩ := hb s
  cases he with
  | @seq _ _ _ s₂ _ _ _ h₁ h₂ =>
    have e : s₂ = s₁ := (Exec.det h₁ e₁).2
    subst e
    have hx' : (R s₂).Contains x 1 := by rw [hR _ _ hf]; exact hx
    unfold Code.iteCold at h₂
    cases h₂ with
    | iteT hev hth =>
      cases hth with
      | seq h₃ h₄ =>
        obtain ⟨-, rfl⟩ := Exec.det h₃ (Exec.seq (Exec.block rfl) (Exec.block rfl))
        have hpt : p (s.gpr .r9) = true := by rw [hq] at hev; exact Option.some.inj hev
        simp only [hpt, ↓reduceIte]
        rw [ha _ _ _ (hP _ _ hf hs) h₄ x hx', hLa _ _ hf, hf.mem]
    | iteF hev hel =>
      have hpf : p (s.gpr .r9) = false := by rw [hq] at hev; exact Option.some.inj hev
      simp only [hpf, Bool.false_eq_true, ↓reduceIte]
      rw [hc _ _ _ (hP _ _ hf hs) hel x hx', hLc _ _ hf, hf.mem]

/-! ## `seal` -/

/-- The code of `seal`'s body in its frame (`Shared.body`): the stitched code
with the AVX2 implementation of `vg_poly1305_blocks`, else `«seal»`. -/
abbrev sealIn (v : XorImpl) : Prog isa :=
  if v.poly = .avx2 then Impl.ChaCha20Poly1305.X86_64.Stitch.sealStitched { v.callee with pass := 512 } .avx2
  else «seal» v.callee v.poly

/-- `sealIn` leaves the keystream area of its context as `ksL` says. -/
theorem sealIn_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State) (hs : sealX86_64.pre s)
    (he : Exec isa (sealIn v) s t u) (x : Addr) (hx : (ksR (cx s)).Contains x 1) :
    u.mem x = (ksL v (cx s) (L s) x).getD (s.mem x) := by
  by_cases hv : v.poly = .avx2
  · have hk := Stitch.sealStitched_correctK v hv (APre.of s hs)
    rw [hv] at hk
    obtain ⟨t', u', he', -, -, k⟩ := hk
    simp only [sealIn, hv, ↓reduceIte] at he
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact ksLeftAt_leaves k hx
  · obtain ⟨t', u', he', -, -, k⟩ := seal_correctK v (APre.of s hs)
    simp only [sealIn, hv, ↓reduceIte] at he
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact ksLeftAt_leaves (k.z hv) hx

theorem sealIn_verified (v : XorImpl) :
    Verified X86_64.target (sealIn v) (sealScratchContract X86_64.abi 212 24) := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.sealS_verified v hv
    rw [hv] at h
    simpa only [sealIn, hv, ↓reduceIte] using h
  · simpa only [sealIn, hv, ↓reduceIte] using seal_verified v

theorem sealIn_sp (v : XorImpl) : (sealIn v).all (fun i => !isa.writesSp i) = true := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.sealS_spSafe v hv
    rw [hv] at h
    simpa only [sealIn, hv, ↓reduceIte] using h
  · simpa only [sealIn, hv, ↓reduceIte] using seal_spSafe v

theorem sealIn_depth (v : XorImpl) : (sealIn v).x86_64Depth ≤ 24 := by
  by_cases hv : v.poly = .avx2
  · have h := Stitch.sealS_xdepth v
    rw [hv] at h
    simpa only [sealIn, hv, ↓reduceIte] using h
  · simpa only [sealIn, hv, ↓reduceIte] using seal_xdepth v

/-- In its frame (`framed`), from the state the frame is entered in: its
context is at `rsp - 1728 + 24`, of which the frame wipes the first 672
bytes. -/
theorem frameW_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s)
    (he : Exec isa (framed (sealIn v)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1) :
    u.mem x = (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat x).getD
      (s.mem x) := by
  have hs' : (Spec.ChaCha20Poly1305.sealSig.contract abi (Curry.const (fun _ => True) _)
      (Spec.ChaCha20Poly1305.sealPost abi.ptrBits) true (24 + 1728) none).pre s := hs
  obtain ⟨hg, -, hl, hf⟩ := narrowS_args (sig := Spec.ChaCha20Poly1305.sealSig) (e := .u64) (n := 212)
    (by decide) (by decide) (by decide) hs'
  have hcx : cx (narrowS Spec.ChaCha20Poly1305.sealSig .u64 212 1728 s) =
      s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24 := hl
  have hL : L (narrowS Spec.ChaCha20Poly1305.sealSig .u64 212 1728 s) = (s.gpr .r9).toNat := by
    show ((narrowS _ _ _ _ s).gpr .r9).toNat = _; rw [hg _ (by decide) (by decide)]
  obtain ⟨hz, hk⟩ := framedW_leaves (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64) (n := 212)
    (bytes := 1728) (stack := 24) (k := 42) (sealIn_verified v) (P := sealX86_64.pre) (fun s h => seal_implies.pre s h)
    (R := fun s => ksR (cx s)) (L := fun s => ksL v (cx s) (L s)) (sealIn_leaves v)
    (by decide) (by decide) (by decide) (sealIn_sp v) (sealIn_depth v) (by decide) (pre_local _ _) hs' he
  rw [show 16 + 8 * nStack Spec.ChaCha20Poly1305.sealSig = 24 by decide] at hz hk
  refine ctx_leaves hz (fun x hx => ?_) hx
  have h := hk x (by rw [hcx]; exact hx) (ks_not_wiped hx)
  rw [hcx, hL] at h
  rw [h]
  congr 1
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hx hc
  rw [Offset.add_add] at hx
  rw [show nStack Spec.ChaCha20Poly1305.sealSig = 1 by decide, show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
  have h₁ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1728) (d := 24 + 672) (n := 1024) (by decide)).1
    (by omega_using [hx])
  have h₂ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1728) (d := 8) (n := 16) (by decide)).1
    (by omega_using [hc])
  omega_using [h₁, h₂]

/-- Through `forward`, from the entry: the context is at `rsp - 1720`. -/
theorem bodyCall_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s)
    (he : Exec isa (bodyCall v.callee v.poly) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1720)).Contains x 1) :
    u.mem x = (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat x).getD (s.mem x) := by
  have hs' : (Spec.ChaCha20Poly1305.sealSig.contract abi (Curry.const (fun _ => True) _)
      (Spec.ChaCha20Poly1305.sealPost abi.ptrBits) true (1752 + 8 + 8) none).pre s := hs
  have hb : body v.callee v.poly = framed (sealIn v) := rfl
  obtain ⟨hrsp, hg, -, -, hf⟩ := narrowF_facts (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8)
    (by decide) (by decide) (by decide) hs'
  have hC : (narrowF Spec.ChaCha20Poly1305.sealSig 8 s).gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24 =
      s.gpr .rsp - BitVec.ofNat 64 1720 := by
    rw [hrsp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub, BitVec.sub_sub, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add, sub_add_ofNat _ (by decide)]
  have h := forward_leaves (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8) (stack := 1752)
    (name := bodyName true v.callee v.poly) (Shared.body_verified v) (P := fun s => (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s)
    (fun _ h => h)
    (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24))
    (L := fun s => ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat)
    (fun s t u hs he => by rw [hb] at he; exact frameW_leaves v s t u hs he)
    (by decide) (by decide) (by decide) (by decide) (Shared.body_sp v) (Shared.body_depth v)
    (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp) hs' he x (by simp only [hC]; exact hx)
  simp only [hC, hg .r9 (by decide) (by decide)] at h
  rw [h]
  congr 1
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hx hc
  rw [show nStack Spec.ChaCha20Poly1305.sealSig = 1 by decide, show (8 : Addr) = BitVec.ofNat 64 8 from rfl,
    BitVec.sub_sub, BitVec.ofNat_add_ofNat] at hc
  have hc' : (x - (s.gpr .rsp - BitVec.ofNat 64 1720 + BitVec.ofNat 64 1704)).toNat < 16 := by
    rw [sub_add_ofNat _ (show 1704 ≤ 1720 by decide)]
    show (x - (s.gpr .rsp - BitVec.ofNat 64 16)).toNat < 16
    have : (x - (s.gpr .rsp - BitVec.ofNat 64 16)).toNat + 1 ≤ 8 * 1 + 8 := hc
    omega_using [this]
  have h₂ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1720) (d := 1704) (n := 16) (by decide)).1 hc'
  omega_using [hx, h₂]

/-- The granules of a clearing of `n` bytes below `rsp` (`n % 16 = 8`: an
8-byte one at the bottom, then 16-byte ones from offset 8) but those wholly
in `[a, b)` from the bottom. -/
def ksGran (n a b : Nat) : List Nat :=
  0 :: ((List.range (n / 16)).filter (fun t => !(decide (a ≤ 8 + 16 * t) && decide (24 + 16 * t ≤ b)))).map
    (8 + 16 * ·)

/-- A byte the clearing of `ksGran n a b` does not zero is in `[a, b)`. -/
theorem ksGran_cov {n a b i : Nat} (h8 : n % 16 = 8) (hi : i < n) (hc : ¬ cov (ksGran n a b) [n] i = true) :
    a ≤ i ∧ i < b := by
  simp only [cov, covC, List.sum_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Nat.zero_add, h8,
    Bool.and_eq_true, not_and] at hc
  have hc := hc (decide_eq_true hi)
  split at hc
  · exact absurd (by simp [ksGran]) hc
  · rename_i hge
    have ht : (i - 8) / 16 < n / 16 := by omega_using [hi, h8, hge]
    by_contra hn
    apply hc
    apply List.contains_iff_mem.mpr
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(i - 8) / 16, List.mem_filter.mpr ⟨List.mem_range.mpr ht, ?_⟩, rfl⟩)
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra hk
    simp only [not_or, Decidable.not_not] at hk
    omega_using [hk, hn, hge]

/-- A byte of the `n` below `R` that the clearing of `ksGran n a b` does not
zero is `[a, b)` above their bottom. -/
theorem ksWindow {n a b : Nat} (h8 : n % 16 = 8) (hch : chunks n = [n]) {R x : Addr}
    (hx : (⟨R - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1) (hw : ¬ WCov (ksGran n a b) (chunks n) R x) :
    a ≤ (x - (R - BitVec.ofNat 64 n)).toNat ∧ (x - (R - BitVec.ofNat 64 n)).toNat < b := by
  rw [hch] at hw
  simp only [WCov, List.sum_cons, List.sum_nil, Nat.add_zero] at hw
  simp only [Region.Contains] at hx
  exact ksGran_cov h8 (by omega_using [hx]) fun hc => hw ⟨by simp only [Region.Contains]; exact hx, hc⟩

/-- The bytes of `seal`'s stack the clearing keeps, below `R`, its stack
pointer on entry: `[R - 1704, R - 24)`, in its context wherever its code has
it (at `R - 1720` after `bodyCall`'s `forward`, at `R - 1704` in the frame of
AVX-512VL's inline code). -/
abbrev sR (R : Addr) : Region := ⟨R - BitVec.ofNat 64 1704, 1680⟩

theorem sR_ctx {R x : Addr} (hx : (sR R).Contains x 1) :
    (ctxR (R - BitVec.ofNat 64 1720)).Contains x 1 ∧
      (ctxR (R - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1 := by
  simp only [Region.Contains] at hx ⊢
  rw [← Offset.sub_ofNat_eq R (show 1704 ≤ 1728 by decide)]
  refine ⟨?_, by omega_using [hx]⟩
  rw [Offset.sub_ofNat_eq R (show 1704 ≤ 1720 by decide)] at hx
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 1720) (d := 1720 - 1704) (n := 1680) (by decide)).1
    (by omega_using [hx])
  omega_using [this]

/-- The granules `seal`'s clearing wipes: all of the 1768 bytes below `rsp`
but those wholly in `sR`, `[64, 1744)` from their bottom. -/
def sealKs : List Nat := ksGran 1768 64 1744

/-- A byte of the 1768 below `R` that `wipe sealKs` does not zero is in `sR R`. -/
theorem sealWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 1768, 1768⟩ : Region).Contains x 1)
    (hw : ¬ WCov sealKs (chunks 1768) R x) : (sR R).Contains x 1 := by
  have hm := ksWindow (by decide) (by decide) hx hw
  simp only [Region.Contains]
  rw [Offset.sub_ofNat_eq R (show 1704 ≤ 1768 by decide)]
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 1768) (d := 1768 - 1704) (n := 1680) (by decide)).2
    ⟨by omega_using [hm], by omega_using [hm]⟩
  omega_using [this]

/-- The lengths for which the AVX-512 instances run the AVX2 code. -/
def pSmall (v : XorImpl) (n : Addr) : Bool :=
  decide (n.toNat < Stitch.smallLim v.callee.small.vl ∨ (Stitch.winLo ≤ n.toNat ∧ n.toNat < Stitch.winHi))

/-- What `seal` leaves below the stack pointer, run by run: its context as
`ctxL` says, for the code its length chooses. -/
def sealV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  if v.poly = .avx512 then
    if pSmall v (s.gpr .r9) then ctxL v.small (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat
    else if v.callee.vl then ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat
    else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat
  else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat

theorem sealCode_ne {v : XorImpl} (hb : ¬ v.poly = .avx512) :
    sealCode v.callee v.poly = bodyCall v.callee v.poly := by
  revert hb
  generalize v.poly = b
  intro hb
  cases b <;> first | exact absurd rfl hb | rfl

/-- What `seal` leaves in `sR`: as `sealV` says. -/
theorem sealCode_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s) (he : Exec isa (sealCode v.callee v.poly) s t u)
    (x : Addr) (hx : (sR (s.gpr .rsp)).Contains x 1) : u.mem x = (sealV v s x).getD (s.mem x) := by
  by_cases hb : v.poly = .avx512
  · have hc : sealCode v.callee v.poly = .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (smallCall v.callee.small) (largeCode v.callee)) := by rw [hb]; rfl
    rw [hc] at he
    have h := choose_leaves (P := fun s => (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s)
      (R := fun s => sR (s.gpr .rsp))
      (La := fun s => ctxL v.small (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat)
      (Lc := fun s => if v.callee.vl then ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat
        else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat)
      (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (fun _ _ hf hs => Shared.flags_pre true hf hs)
      (fun _ _ hf => by simp only [hf.gpr .rsp (by decide) (by decide)])
      (fun _ _ hf => by simp only [hf.gpr .rsp (by decide) (by decide), hf.gpr .r9 (by decide) (by decide)])
      (fun _ _ hf => by simp only [hf.gpr .rsp (by decide) (by decide), hf.gpr .r9 (by decide) (by decide)])
      (fun s t u hs he x hx => by
        have he' : Exec isa (bodyCall v.small.callee v.small.poly) s t u := by
          rw [XorImpl.small_callee, v.small_poly]; exact he
        exact bodyCall_leaves v.small s t u hs he' x (sR_ctx hx).1)
      (fun s t u hs he x hx => by
        unfold largeCode at he
        split at he
        · next hvl =>
          simp only [hvl, ↓reduceIte]
          have he' : Exec isa (framed (sealIn v)) s t u := by
            simp only [sealIn, hb, reduceCtorEq, ↓reduceIte]; exact he
          exact frameW_leaves v s t u (Shared.pre_old true hs) he' x (sR_ctx hx).2
        · next hvl =>
          simp only [hvl, Bool.false_eq_true, ↓reduceIte]
          have he' : Exec isa (bodyCall v.callee v.poly) s t u := by rw [hb]; exact he
          exact bodyCall_leaves v s t u hs he' x (sR_ctx hx).1)
      hs he x hx
    simp only [sealV, hb, ↓reduceIte]
    exact h
  · rw [sealCode_ne hb] at he
    simp only [sealV, hb, ↓reduceIte]
    exact bodyCall_leaves v s t u hs he x (sR_ctx hx).1

/-- Two runs of `seal` leave the same bytes in their stack but the granules
`sealKs`: as `sealV` says. -/
theorem seal_resOk (v : XorImpl) :
    ResOk (sealCode v.callee v.poly) (Spec.ChaCha20Poly1305.sealContract abi 1768) 1768 sealKs (chunks 1768) := by
  unfold Spec.ChaCha20Poly1305.sealContract
  refine resOk_of_leaves (V := sealV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact sealCode_leaves v s t u hs he x (sealWindow hx hw)
  · intro s₁ s₂ _ _ _ ho _
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    simp only [sealV, hg .rsp (by decide), hg .r9 (by decide)]

/-- `seal`'s postcondition reads the memory on return only within the
buffers: the data and the tag. -/
theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

/-- `seal` of an instance, unscrubbed. -/
def sealPlain (v : XorImpl) : Registration Spec.ChaCha20Poly1305.sealApi X86_64.target where
  suffix := v.suffix
  code := sealCode v.callee v.poly
  verified := Shared.seal_verified v
  spSafe := Shared.seal_sp v

/-- `seal` of an instance, followed by the clearing of all of its stack but
its context (`sealKs`), and so without secret residue (`seal_resOk`). -/
def sealReg (v : XorImpl) : Registration Spec.ChaCha20Poly1305.sealApi X86_64.target :=
  RScrub.withScrubResM (sealPlain v) (sealOut _) sealKs (seal_resOk v)

/-! ## `open` -/

/-- `open`'s call (`openCall`) leaves the keystream area of `work` as `ksL`
says (`CallOpen.callOpen_okK`). -/
theorem openCall_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : Shared.openK.pre s) (he : Exec isa (openCall v.callee v.poly) s t u) (x : Addr)
    (hx : (ksR (stackArg s 1)).Contains x 1) :
    u.mem x = (ksL v (stackArg s 1) (s.gpr .r9).toNat x).getD (s.mem x) := by
  have hs' : Shared.openPre s := hs
  have hw : WP isa (openCall v.callee v.poly) s fun z =>
      KsLeftZ v (stackArg s 1) (s.gpr .r9).toNat s.mem z.mem := by
    refine WP.seq (WP.mono (Shared.openArgs_ok hs') fun h hh => ?_)
    refine WP.mono (CallOpen.callOpen_okK v (Shared.ocpre_of hs' hh)) fun z ⟨_, hk⟩ => ?_
    have e₁ : CallOpen.hW h = stackArg s 1 := hh.rax
    have e₂ : CallOpen.hL h = (s.gpr .r9).toNat := by show (h.gpr .r9).toNat = _; rw [hh.r9]
    rw [e₁, e₂, hh.mem] at hk
    exact hk
  obtain ⟨t', u', he', hk⟩ := hw
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact ksLeftAt_leaves hk hx

/-- In its frame (`framed`): its context is at `rsp - 1728 + 24`, of which
the frame wipes the first 672 bytes. -/
theorem frameO_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s)
    (he : Exec isa (framed (openCall v.callee v.poly)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1) :
    u.mem x = (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat x).getD
      (s.mem x) := by
  have hs' : (Spec.ChaCha20Poly1305.openSig.contract abi (Curry.const (fun _ => True) _)
      (Spec.ChaCha20Poly1305.openZeroPost abi.ptrBits) true (56 + 1728)
      (some (Spec.ChaCha20Poly1305.openLeak abi.ptrBits))).pre s := hs
  obtain ⟨hg, -, hl, hf⟩ := narrowS_args (sig := Spec.ChaCha20Poly1305.openSig) (e := .u64) (n := 212)
    (by decide) (by decide) (by decide) hs'
  have hcx : stackArg (narrowS Spec.ChaCha20Poly1305.openSig .u64 212 1728 s) 1 =
      s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24 := hl
  have hL : ((narrowS Spec.ChaCha20Poly1305.openSig .u64 212 1728 s).gpr .r9).toNat = (s.gpr .r9).toNat := by
    rw [hg _ (by decide) (by decide)]
  obtain ⟨hz, hk⟩ := framedW_leaves (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (bytes := 1728) (stack := 56) (k := 42) (Shared.openCall_verified v) (P := Shared.openK.pre)
    (fun s h => Shared.openCall_implies.pre s h)
    (R := fun s => ksR (stackArg s 1)) (L := fun s => ksL v (stackArg s 1) (s.gpr .r9).toNat)
    (openCall_leaves v) (by decide) (by decide) (by decide) (Shared.openCall_spSafe v)
    (Shared.openCall_xdepth v) (by decide) (pre_local _ _) hs' he
  rw [show 16 + 8 * nStack Spec.ChaCha20Poly1305.openSig = 24 by decide] at hz hk
  refine ctx_leaves hz (fun x hx => ?_) hx
  have h := hk x (by rw [hcx]; exact hx) (ks_not_wiped hx)
  rw [hcx, hL] at h
  rw [h]
  congr 1
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hx hc
  rw [Offset.add_add] at hx
  rw [show nStack Spec.ChaCha20Poly1305.openSig = 1 by decide, show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
  have h₁ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1728) (d := 24 + 672) (n := 1024) (by decide)).1
    (by omega_using [hx])
  have h₂ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1728) (d := 8) (n := 16) (by decide)).1
    (by omega_using [hc])
  omega_using [h₁, h₂]

/-- The granules `open`'s clearing wipes: all of the 1784 bytes below `rsp`
but those wholly in the context, `[80, 1776)` from their bottom. -/
def openKs : List Nat := ksGran 1784 80 1776

theorem openWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 1784, 1784⟩ : Region).Contains x 1)
    (hw : ¬ WCov openKs (chunks 1784) R x) :
    (ctxR (R - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1 := by
  have hm := ksWindow (by decide) (by decide) hx hw
  simp only [Region.Contains]
  rw [Offset.sub_ofNat_eq R (show 1728 ≤ 1784 by decide), Offset.add_add]
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 1784) (d := 1784 - 1728 + 24) (n := 1696) (by decide)).2
    ⟨by omega_using [hm], by omega_using [hm]⟩
  omega_using [this]

/-- What `open` leaves below the stack pointer, run by run: its context as
`ctxL` says, for the code its length chooses. -/
def openV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  if v.poly = .avx512 then
    if pSmall v (s.gpr .r9) then ctxL v.small (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat
    else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat
  else if v.poly = .ifma then
    if decide (Stitch.ifmaLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < Stitch.ifmaHi) then
      ctxL XorImpl.avx512vl.small (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat
    else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat
  else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat

/-- What `open` leaves in its context: as `openV` says. -/
theorem openCode_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s) (he : Exec isa (openCode v.callee v.poly) s t u)
    (x : Addr) (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1) :
    u.mem x = (openV v s x).getD (s.mem x) := by
  have hR : ∀ s u : State, Stitch.FlagsOnly s u →
      ctxR (u.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) =
        ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) := fun _ _ hf => by
    simp only [hf.gpr .rsp (by decide) (by decide)]
  have hL : ∀ (w : XorImpl) (s u : State), Stitch.FlagsOnly s u →
      ctxL w (u.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (u.gpr .r9).toNat =
        ctxL w (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat := fun _ _ _ hf => by
    simp only [hf.gpr .rsp (by decide) (by decide), hf.gpr .r9 (by decide) (by decide)]
  by_cases hb : v.poly = .avx512
  · have hc : openCode v.callee v.poly = .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (framed (openCall v.callee.small .avx2)) (framed (openCall v.callee .avx512))) := by
      rw [hb]; rfl
    rw [hc] at he
    have h := choose_leaves (P := fun s => (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s)
      (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24))
      (La := fun s => ctxL v.small (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat)
      (Lc := fun s => ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat)
      (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (fun _ _ hf hs => Shared.flags_pre false hf hs) hR (hL _) (hL _)
      (fun s t u hs he x hx => by
        have he' : Exec isa (framed (openCall v.small.callee v.small.poly)) s t u := by
          rw [XorImpl.small_callee, v.small_poly]; exact he
        exact frameO_leaves v.small s t u hs he' x hx)
      (fun s t u hs he x hx => by
        have he' : Exec isa (framed (openCall v.callee v.poly)) s t u := by rw [hb]; exact he
        exact frameO_leaves v s t u hs he' x hx)
      hs he x hx
    simp only [openV, hb, ↓reduceIte]
    exact h
  · by_cases hi : v.poly = .ifma
    · have hc : openCode v.callee v.poly = .seq (.block Stitch.ifmaTest)
          (Code.iteCold .b (framed (openCall Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2))
            (framed (openCall v.callee .ifma))) := by
        rw [hi]; rfl
      rw [hc] at he
      have h := choose_leaves (P := fun s => (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s)
        (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24))
        (La := fun s => ctxL XorImpl.avx512vl.small (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)
          (s.gpr .r9).toNat)
        (Lc := fun s => ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat)
        (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
        (fun _ _ hf hs => Shared.flags_pre false hf hs) hR (hL _) (hL _)
        (fun s t u hs he x hx => by
          have he' : Exec isa (framed (openCall XorImpl.avx512vl.small.callee XorImpl.avx512vl.small.poly)) s t u := by
            rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly]; exact he
          exact frameO_leaves XorImpl.avx512vl.small s t u hs he' x hx)
        (fun s t u hs he x hx => by
          have he' : Exec isa (framed (openCall v.callee v.poly)) s t u := by rw [hi]; exact he
          exact frameO_leaves v s t u hs he' x hx)
        hs he x hx
      simp only [openV, hi, ↓reduceIte]
      exact h
    · have hc : openCode v.callee v.poly = framed (openCall v.callee v.poly) := by
        revert hb hi
        generalize v.poly = b
        intro hb hi
        cases b <;> first | exact absurd rfl hb | exact absurd rfl hi | rfl
      rw [hc] at he
      simp only [openV, hb, hi, ↓reduceIte]
      exact frameO_leaves v s t u hs he x hx

theorem open_resOk (v : XorImpl) :
    ResOk (openCode v.callee v.poly) (Spec.ChaCha20Poly1305.openZeroContract abi 1784) 1784 openKs
      (chunks 1784) := by
  unfold Spec.ChaCha20Poly1305.openZeroContract
  refine resOk_of_leaves (V := openV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact openCode_leaves v s t u hs he x (openWindow hx hw)
  · intro s₁ s₂ _ _ _ ho _
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    simp only [openV, hg .rsp (by decide), hg .r9 (by decide)]

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

def openPlain (v : XorImpl) : Registration Spec.ChaCha20Poly1305.openZeroApi X86_64.target where
  suffix := v.suffix
  code := openCode v.callee v.poly
  verified := Shared.open_verified v
  spSafe := Shared.open_sp v

/-- `open` of an instance, followed by the clearing of all of its stack but
its context (`openKs`). -/
def openReg (v : XorImpl) : Registration Spec.ChaCha20Poly1305.openZeroApi X86_64.target :=
  RScrub.withScrubResM (openPlain v) (openOut _) openKs (open_resOk v)

/-! ## `open_to` -/

/-- `open_to`'s code in its frame (`OpenTo.body`) leaves the keystream area of
`work` (its stack argument 3) as `ksL` says. -/
theorem toBody_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : OpenTo.toK.pre s) (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly) s t u)
    (x : Addr) (hx : (ksR (stackArg s 3)).Contains x 1) :
    u.mem x = (ksL v (stackArg s 3) (s.gpr .r9).toNat x).getD (s.mem x) := by
  have hs' : OpenTo.TPre s := hs
  have hw : WP isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly) s fun z =>
      KsLeftZ v (stackArg s 3) (s.gpr .r9).toNat s.mem z.mem := by
    refine WP.seq (WP.mono (OpenTo.toArgs_ok hs') fun h hh => ?_)
    refine WP.mono (CallOpen.callOpen_okK v (OpenTo.cpre_of hs' hh)) fun z ⟨_, hk⟩ => ?_
    have e₁ : CallOpen.hW h = stackArg s 3 := hh.rax
    have e₂ : CallOpen.hL h = (s.gpr .r9).toNat := by show (h.gpr .r9).toNat = _; rw [hh.r9]
    rw [e₁, e₂, hh.mem] at hk
    exact hk
  obtain ⟨t', u', he', hk⟩ := hw
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact ksLeftAt_leaves hk hx

/-- In its frame (`OpenTo.scratched`): its context is at `rsp - 1744 + 40`,
of which the frame wipes the first 672 bytes. -/
theorem frameT_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s)
    (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
      (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40)).Contains x 1) :
    u.mem x = (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat x).getD
      (s.mem x) := by
  have hs' : (Spec.ChaCha20Poly1305.openToSig.contract abi (Spec.ChaCha20Poly1305.openToPre abi.ptrBits)
      (Spec.ChaCha20Poly1305.openToPost abi.ptrBits) true (56 + 1744)
      (some (Spec.ChaCha20Poly1305.openToLeak abi.ptrBits))).pre s := hs
  obtain ⟨hg, -, hl, hf⟩ := narrowS_args (sig := Spec.ChaCha20Poly1305.openToSig) (e := .u64) (n := 212)
    (by decide) (by decide) (by decide) hs'
  have hcx : stackArg (narrowS Spec.ChaCha20Poly1305.openToSig .u64 212 1744 s) 3 =
      s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40 := hl
  have hL : ((narrowS Spec.ChaCha20Poly1305.openToSig .u64 212 1744 s).gpr .r9).toNat = (s.gpr .r9).toNat := by
    rw [hg _ (by decide) (by decide)]
  obtain ⟨hz, hk⟩ := framedW_leaves (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 212) (bytes := 1744) (stack := 56) (k := 42) (OpenTo.body_verified v) (P := OpenTo.toK.pre)
    (fun s h => OpenTo.to_implies.pre s h)
    (R := fun s => ksR (stackArg s 3)) (L := fun s => ksL v (stackArg s 3) (s.gpr .r9).toNat)
    (toBody_leaves v) (by decide) (by decide) (by decide) (OpenTo.body_spSafe v)
    (OpenTo.body_xdepth v) (by decide) (openToPre_local _) hs' he
  rw [show 16 + 8 * nStack Spec.ChaCha20Poly1305.openToSig = 40 by decide] at hz hk
  refine ctx_leaves hz (fun x hx => ?_) hx
  have h := hk x (by rw [hcx]; exact hx) (ks_not_wiped hx)
  rw [hcx, hL] at h
  rw [h]
  congr 1
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hx hc
  rw [Offset.add_add] at hx
  rw [show nStack Spec.ChaCha20Poly1305.openToSig = 3 by decide, show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
  have h₁ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1744) (d := 40 + 672) (n := 1024) (by decide)).1
    (by omega_using [hx])
  have h₂ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1744) (d := 8) (n := 32) (by decide)).1
    (by omega_using [hc])
  omega_using [h₁, h₂]

/-- The granules `open_to`'s clearing wipes: all of the 1800 bytes below
`rsp` but those wholly in the context, `[96, 1792)` from their bottom. -/
def openToKs : List Nat := ksGran 1800 96 1792

theorem openToWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 1800, 1800⟩ : Region).Contains x 1)
    (hw : ¬ WCov openToKs (chunks 1800) R x) :
    (ctxR (R - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40)).Contains x 1 := by
  have hm := ksWindow (by decide) (by decide) hx hw
  simp only [Region.Contains]
  rw [Offset.sub_ofNat_eq R (show 1744 ≤ 1800 by decide), Offset.add_add]
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 1800) (d := 1800 - 1744 + 40) (n := 1696) (by decide)).2
    ⟨by omega_using [hm], by omega_using [hm]⟩
  omega_using [this]

/-- What `open_to` leaves below the stack pointer, run by run: as `open`'s,
with its context at `rsp - 1744 + 40`. -/
def openToV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  if v.poly = .avx512 then
    if pSmall v (s.gpr .r9) then ctxL v.small (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat
    else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat
  else if v.poly = .ifma then
    if decide (Stitch.ifmaLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < Stitch.ifmaHi) then
      ctxL XorImpl.avx512vl.small (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat
    else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat
  else ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat

theorem openTo_flags {s u : State} (hf : Stitch.FlagsOnly s u)
    (hs : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s) :
    (Spec.ChaCha20Poly1305.openToContract abi 1800).pre u :=
  Shared.flags_pre_sig (sig := Spec.ChaCha20Poly1305.openToSig)
    (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
    (stack := 1800) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) hf hs

/-- What `open_to` leaves in its context: as `openToV` says. -/
theorem openToCode_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s)
    (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly) s t u)
    (x : Addr) (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40)).Contains x 1) :
    u.mem x = (openToV v s x).getD (s.mem x) := by
  have hR : ∀ s u : State, Stitch.FlagsOnly s u →
      ctxR (u.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) =
        ctxR (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) := fun _ _ hf => by
    simp only [hf.gpr .rsp (by decide) (by decide)]
  have hL : ∀ (w : XorImpl) (s u : State), Stitch.FlagsOnly s u →
      ctxL w (u.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (u.gpr .r9).toNat =
        ctxL w (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat := fun _ _ _ hf => by
    simp only [hf.gpr .rsp (by decide) (by decide), hf.gpr .r9 (by decide) (by decide)]
  by_cases hb : v.poly = .avx512
  · have hc : Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly =
        .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee.small .avx2))
          (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee .avx512))) := by
      rw [hb]; rfl
    rw [hc] at he
    have h := choose_leaves (P := fun s => (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s)
      (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40))
      (La := fun s => ctxL v.small (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat)
      (Lc := fun s => ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat)
      (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (fun _ _ hf hs => openTo_flags hf hs) hR (hL _) (hL _)
      (fun s t u hs he x hx => by
        have he' : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.small.callee v.small.poly)) s t u := by
          rw [XorImpl.small_callee, v.small_poly]; exact he
        exact frameT_leaves v.small s t u hs he' x hx)
      (fun s t u hs he x hx => by
        have he' : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly)) s t u := by rw [hb]; exact he
        exact frameT_leaves v s t u hs he' x hx)
      hs he x hx
    simp only [openToV, hb, ↓reduceIte]
    exact h
  · by_cases hi : v.poly = .ifma
    · have hc : Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly = .seq (.block Stitch.ifmaTest)
          (Code.iteCold .b (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
              (Impl.ChaCha20Poly1305.X86_64.OpenTo.body Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2))
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
              (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee .ifma))) := by
        rw [hi]; rfl
      rw [hc] at he
      have h := choose_leaves (P := fun s => (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s)
        (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40))
        (La := fun s => ctxL XorImpl.avx512vl.small (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40)
          (s.gpr .r9).toNat)
        (Lc := fun s => ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat)
        (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
        (fun _ _ hf hs => openTo_flags hf hs) hR (hL _) (hL _)
        (fun s t u hs he x hx => by
          have he' : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
              (Impl.ChaCha20Poly1305.X86_64.OpenTo.body XorImpl.avx512vl.small.callee XorImpl.avx512vl.small.poly))
              s t u := by
            rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly]; exact he
          exact frameT_leaves XorImpl.avx512vl.small s t u hs he' x hx)
        (fun s t u hs he x hx => by
          have he' : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
              (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly)) s t u := by rw [hi]; exact he
          exact frameT_leaves v s t u hs he' x hx)
        hs he x hx
      simp only [openToV, hi, ↓reduceIte]
      exact h
    · have hc : Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly =
          Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly) := by
        revert hb hi
        generalize v.poly = b
        intro hb hi
        cases b <;> first | exact absurd rfl hb | exact absurd rfl hi | rfl
      rw [hc] at he
      simp only [openToV, hb, hi, ↓reduceIte]
      exact frameT_leaves v s t u hs he x hx

theorem openTo_resOk (v : XorImpl) :
    ResOk (Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly)
      (Spec.ChaCha20Poly1305.openToContract abi 1800) 1800 openToKs (chunks 1800) := by
  unfold Spec.ChaCha20Poly1305.openToContract
  refine resOk_of_leaves (V := openToV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact openToCode_leaves v s t u hs he x (openToWindow hx hw)
  · intro s₁ s₂ _ _ _ ho _
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    simp only [openToV, hg .rsp (by decide), hg .r9 (by decide)]

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain (openToPost_out _)

def openToPlain (v : XorImpl) : Registration Spec.ChaCha20Poly1305.openToApi X86_64.target where
  suffix := v.suffix
  code := Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly
  verified := OpenTo.openTo_verified v
  spSafe := OpenTo.openTo_sp v

/-- `open_to` of an instance, followed by the clearing of all of its stack but
its context (`openToKs`). -/
def openToReg (v : XorImpl) : Registration Spec.ChaCha20Poly1305.openToApi X86_64.target :=
  RScrub.withScrubResM (openToPlain v) (openToOut _) openToKs (openTo_resOk v)

/-! ## `seal_gather` -/

/-- What `seal` leaves, as `seal_gather` needs it of its callee (`SealFn.E`). -/
def sealE (v : XorImpl) (s : State) (m : Mem) : Prop :=
  ∀ x, (ctxR (s.gpr .rsp - BitVec.ofNat 64 1720)).Contains x 1 →
    m x = (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat x).getD (s.mem x)

/-- `seal_gather`'s callee, with what it leaves (`bodyCall_leaves`). -/
def sealFnL (v : XorImpl) (hv : ¬ v.poly = .avx512) : Gather.Whole.SealFn :=
  { Gather.Whole.sealFn v with
    E := sealE v
    exec := fun s h => by
      obtain ⟨t, s', e, a, p⟩ := (Shared.seal_verified v).1 s h
      refine ⟨t, s', e, a, p, fun x hx => ?_⟩
      change Exec isa (sealCode v.callee v.poly) s t s' at e
      rw [sealCode_ne hv] at e
      exact bodyCall_leaves v s t s' h e x hx }

/-- The instances whose `seal_gather` gathers the whole data before one call
of `seal` (`Gather.gatherCode`). -/
abbrev Whole (v : XorImpl) : Prop := ¬ v.poly = .avx512 ∧ ¬ v.poly = .ifma

open Gather.Whole in
/-- `seal_gather` leaves its callee's context, at `rsp - 1832 + 48`, as
`ctxL` says. -/
theorem gather_leaves (v : XorImpl) (hv : Whole v) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.sealGatherContract abi 1880).pre s) (he : Exec isa (Gather.gatherCode v) s t u)
    (x : Addr) (hx : (ctxR (Bs s + BitVec.ofNat 64 48)).Contains x 1) :
    u.mem x = (ctxL v (Bs s + BitVec.ofNat 64 48) (stackArg s 1).toNat x).getD (s.mem x) := by
  have hp : Gather.Whole.gatherPre s :=
    Gather.whole_pre (s := s) (e := s) ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Gather.gather_implies.pre s hs)
  have h := lay hp
  have hgc : Gather.gatherCode v = Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole (Gather.width v)
      (sealFnL v hv.1).name (sealFnL v hv.1).code := by
    unfold Gather.gatherCode; split
    · next hb => exact absurd hb hv.1
    · next hb => exact absurd hb hv.2
    · rfl
  rw [hgc] at he
  obtain ⟨t', u', he', c, hc, hE⟩ := sealGather_wpE (Gather.width v) (sealFnL v hv.1) hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  have hsp : (xS s c).gpr .rsp - BitVec.ofNat 64 1720 = Bs s + BitVec.ofNat 64 48 := by
    rw [hc.xsp, add_ofNat_sub_ofNat _ (show 1720 ≤ 1768 by decide)]
  have hr9 : (xS s c).gpr .r9 = stackArg s 1 := by rw [xgpr_eq (by decide), hc.r9]
  have hE' := hE x (by rw [hsp]; exact hx)
  rw [hsp, hr9] at hE'
  rw [hE']
  refine ctxL_congr fun hk => ?_
  -- The callee's memory on entry: ours, with the pushes and the slices gathered elsewhere.
  have h₀ := (Offset.lt_iff x (Bs s) (d := 48) (n := 1696) (by decide)).1 (by
    simp only [Region.Contains] at hx; omega_using [hx])
  have hxB : 720 ≤ (x - Bs s).toNat ∧ (x - Bs s).toNat < 720 + 1024 := by
    refine ⟨?_, by omega_using [h₀]⟩
    by_contra hlt
    exact hk ((Offset.lt_iff x (Bs s) (d := 48) (n := 672) (by decide)).2 ⟨h₀.1, by omega_using [hlt]⟩)
  have hBn := h.hBn
  have nb : ∀ {d n : Nat}, (d + n ≤ 720 ∨ 1744 ≤ d) → d + n ≤ 1864 →
      ¬ (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 := fun {d n} h₁ h₂ hc' => by
    simp only [Region.Contains] at hc'
    have := (Offset.lt_iff x (Bs s) (d := d) (n := n) (by omega_using [h₂])).1 (by omega_using [hc'])
    omega_using [h₁, this, hxB]
  have x₁ : (xS s c).mem x = (qS c).mem x := hc.xmem x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact nb (by decide) (by decide)
  have x₂ : (qS c).mem x = c.mem x := (hc.qmem h).1 x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact nb (by decide) (by decide)
  have x₃ : eM s x = s.mem x := h.frame_eM x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact nb (by decide) (by decide)
  have x₄ : gM s x = eM s x := h.frame_gM x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact bd x (by show (x - Bs s).toNat + 1 ≤ 1832; omega_using [hxB])
  rw [x₁, x₂, hc.mem, x₄, x₃]


/-- `seal_gather`'s postcondition reads the memory on return only within
`dst` and `tag`. -/
theorem sealGatherPost_out (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.ChaCha20Poly1305.sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.ChaCha20Poly1305.sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb) vs m m₁ r →
      Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb)
        vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.ChaCha20Poly1305.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.ChaCha20Poly1305.sealGatherPost, ArgWord.ofRaw] at h ⊢
  intro h₁ h₂
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
  exact h h₁ h₂

/-- The granules `seal_gather`'s clearing wipes: all of the 1880 bytes below
`rsp` but those wholly in its callee's context, `[96, 1792)` from their
bottom. -/
def gatherKs : List Nat := ksGran 1880 96 1792

theorem gatherWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 1880, 1880⟩ : Region).Contains x 1)
    (hw : ¬ WCov gatherKs (chunks 1880) R x) :
    (ctxR (R - BitVec.ofNat 64 1832 + BitVec.ofNat 64 48)).Contains x 1 := by
  have hm := ksWindow (by decide) (by decide) hx hw
  simp only [Region.Contains]
  rw [Offset.sub_ofNat_eq R (show 1832 ≤ 1880 by decide), Offset.add_add]
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 1880) (d := 1880 - 1832 + 48) (n := 1696) (by decide)).2
    ⟨by omega_using [hm], by omega_using [hm]⟩
  omega_using [this]

/-- What `seal_gather` leaves below the stack pointer, run by run. -/
def gatherV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  ctxL v (s.gpr .rsp - BitVec.ofNat 64 1832 + BitVec.ofNat 64 48) (stackArg s 1).toNat

theorem gather_resOk (v : XorImpl) (hv : Whole v) :
    ResOk (Gather.gatherCode v) (Spec.ChaCha20Poly1305.sealGatherContract abi 1880) 1880 gatherKs
      (chunks 1880) := by
  unfold Spec.ChaCha20Poly1305.sealGatherContract
  refine resOk_of_leaves (V := gatherV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact gather_leaves v hv s t u hs he x (gatherWindow hx hw)
  · intro s₁ s₂ _ _ hp ho _
    obtain ⟨-, hpubs, -⟩ := (pubL_args (sig := Spec.ChaCha20Poly1305.sealGatherSig) (by decide)).mp hp
    have hg : ∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r := ho.2.2.1
    have hl : stackArg s₁ 1 = stackArg s₂ 1 := by
      have := hpubs 7 (by decide)
      have e : ∀ s : State, (allArgs Spec.ChaCha20Poly1305.sealGatherSig s).getD 7 0 = stackArg s 1 := fun _ => rfl
      rw [e, e, show ((Spec.ChaCha20Poly1305.sealGatherSig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD 7 64 = 64
        from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq] at this
      exact this
    simp only [gatherV, hg .rsp (by decide), hl]

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealGatherPost_out _)

def gatherPlain (v : XorImpl) : Registration Spec.ChaCha20Poly1305.sealGatherApi X86_64.target where
  suffix := v.suffix
  code := Gather.gatherCode v
  verified := Gather.gather_verified v
  spSafe := Gather.gather_spSafe v

/-- `seal_gather` of an instance that gathers the whole data (`Whole`), calling
`seal`'s code unscrubbed (`…_core`), followed by the clearing of all of its
stack but its callee's context (`gatherKs`); the others as they are. -/
def gatherReg (v : XorImpl) : Registration Spec.ChaCha20Poly1305.sealGatherApi X86_64.target :=
  if hv : Whole v then RScrub.withScrubResM (gatherPlain v) (gatherOut _) gatherKs (gather_resOk v hv)
  else gatherPlain v

end VG.Proof.ChaCha20Poly1305.X86_64.Scrub
