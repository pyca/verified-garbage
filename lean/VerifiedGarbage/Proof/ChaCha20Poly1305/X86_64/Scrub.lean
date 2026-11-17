module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Fn
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Fn
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.By
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Leaves
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
import VerifiedGarbage.Proof.Framework.X86_64.Syms
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

/-- What is left in a context at `C`, through the release of the frame it is
in (`loseL`): zeros in the 672 bytes its frame wipes, and the keystream area
as `ksL` says. -/
theorem ctx_leavesL {v : XorImpl} {C : Addr} {Lx : Nat} {B : Addr} {n : Nat} {U : Nat → BitVec 64}
    {m₀ m : Mem} {x : Addr}
    (hz : (⟨C, 16 * 42⟩ : Region).Contains x 1 → m x = (loseL B n U (fun _ => some 0) x).getD 0)
    (hk : (ksR C).Contains x 1 → m x = (loseL B n U (ksL v C Lx) x).getD (m₀ x))
    (hx : (ctxR C).Contains x 1) : m x = (loseL B n U (ctxL v C Lx) x).getD (m₀ x) := by
  have hs : (x - C).toNat < 672 → (⟨C, 16 * 42⟩ : Region).Contains x 1 := fun h => by
    simp only [Region.Contains]; omega_using [h]
  have hs' : ¬ (x - C).toNat < 672 → (ksR C).Contains x 1 := fun h => by
    simp only [Region.Contains] at hx ⊢
    have := (Offset.lt_iff x C (d := 672) (n := 1024) (by decide)).2 ⟨by omega_using [h], by omega_using [hx]⟩
    omega_using [this]
  rcases loseL_cases B n U x with e | ⟨w, e⟩
  · rw [e] at hz hk ⊢
    simp only [ctxL]
    by_cases h : (x - C).toNat < 672
    · rw [VG.X86_64.Scrub.ite_t h]; exact hz (hs h)
    · rw [VG.X86_64.Scrub.ite_f h]; exact hk (hs' h)
  · rw [e] at hz hk ⊢
    by_cases h : (x - C).toNat < 672
    · exact hz (hs h)
    · exact hk (hs' h)

/-- A byte `[0, n)` above `R - a` is outside the `k` bytes below `R`, if
`n + k ≤ a`. -/
theorem below_out {R x : Addr} {a n k : Nat} (hx : (⟨R - BitVec.ofNat 64 a, n⟩ : Region).Contains x 1)
    (h : n + k ≤ a) (ha : a < 2 ^ 64) : ¬ (x - (R - BitVec.ofNat 64 k)).toNat < k := by
  rw [show R - BitVec.ofNat 64 k = R - BitVec.ofNat 64 a + BitVec.ofNat 64 (a - k) by
    rw [sub_add_ofNat _ (Nat.sub_le a k), Nat.sub_sub_self (by omega_using [h])],
    Offset.toNat_sub_add _ _ (by omega_using [ha])]
  simp only [Region.Contains] at hx
  omega_using [hx, h, ha]

/-- The state after a block, as a function of the state before it. -/
def afterB (b : List Instr) (s : State) : State := ((execBlock isa b s).map Prod.fst).getD s

theorem afterB_eq {b : List Instr} {s u : State} {t : List Leak} (h : Exec isa (.block b) s t u) :
    afterB b s = u := by
  cases h with
  | block h => simp only [afterB, h, Option.map_some, Option.getD_some]

/-- A comparison that writes only flags keeps the unknowns and the functions'
addresses. -/
theorem afterB_facts {b : List Instr} {p : Addr → Bool}
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ Stitch.FlagsOnly s u)
    (s : State) :
    Stitch.FlagsOnly s (afterB b s) ∧ (afterB b s).unknowns = s.unknowns ∧ (afterB b s).syms = s.syms := by
  obtain ⟨t, u, e, -, hf⟩ := hb s
  rw [afterB_eq e]
  cases e with
  | block h => exact ⟨hf, (Scrub.execBlock_unknowns h h).2.1, execBlock_syms h⟩

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
    (ha : ∀ s t u, P s → Exec isa a s t u → ∀ x, (R s).Contains x 1 → u.mem x = (La s x).getD (s.mem x))
    (hc : ∀ s t u, P s → Exec isa c s t u → ∀ x, (R s).Contains x 1 → u.mem x = (Lc s x).getD (s.mem x))
    {s : State} {t : List Leak} {u : State} (hs : P s)
    (he : Exec isa (.seq (.block b) (Code.iteCold .b a c)) s t u) (x : Addr) (hx : (R s).Contains x 1) :
    u.mem x = ((if p (s.gpr .r9) then La (afterB b s) else Lc (afterB b s)) x).getD (s.mem x) := by
  obtain ⟨t₁, s₁, e₁, hq, hf⟩ := hb s
  cases he with
  | @seq _ _ _ s₂ _ _ _ h₁ h₂ =>
    have e : s₂ = s₁ := (Exec.det h₁ e₁).2
    subst e
    have ha' : afterB b s = s₂ := afterB_eq h₁
    have hx' : (R s₂).Contains x 1 := by rw [hR _ _ hf]; exact hx
    unfold Code.iteCold at h₂
    cases h₂ with
    | iteT hev hth =>
      cases hth with
      | seq h₃ h₄ =>
        obtain ⟨-, rfl⟩ := Exec.det h₃ (Exec.seq (Exec.block rfl) (Exec.block rfl))
        have hpt : p (s.gpr .r9) = true := by rw [hq] at hev; exact Option.some.inj hev
        simp only [hpt, ↓reduceIte, ha']
        rw [ha _ _ _ (hP _ _ hf hs) h₄ x hx', hf.mem]
    | iteF hev hel =>
      have hpf : p (s.gpr .r9) = false := by rw [hq] at hev; exact Option.some.inj hev
      simp only [hpf, Bool.false_eq_true, ↓reduceIte, ha']
      rw [hc _ _ _ (hP _ _ hf hs) hel x hx', hf.mem]

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

/-- The unknowns `sealIn` ends with, in its frame (`framed`) entered from `s`:
those its release loses the frame's bytes to (`framedW_leaves`). -/
noncomputable def uW (v : XorImpl) (s : State) : Nat → BitVec 64 :=
  innerU (sealIn v) (narrowS Spec.ChaCha20Poly1305.sealSig .u64 212 1728 s)

/-- What `framed (sealIn v)` leaves, entered from `s`: its context, at
`rsp - 1728 + 24`, as `ctxL` says, through the frame's release. -/
noncomputable def ctxW (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  loseL (s.gpr .rsp - BitVec.ofNat 64 1728) 1728 (uW v s)
    (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat)

theorem uW_agree (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.sealContract abi 1752).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (sealIn v), s₁.syms n = s₂.syms n) : uW v s₁ = uW v s₂ :=
  framed_innerU_agree (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64) (n := 212)
    (bytes := 1728) (stack := 24) (sealIn_verified v) (by decide) (by decide) (by decide) (pre_local _ _)
    h₁ h₂ hp hu hsy

/-- In its frame (`framed`), from the state the frame is entered in: its
context is at `rsp - 1728 + 24`, of which the frame wipes the first 672
bytes. -/
theorem frameW_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s)
    (he : Exec isa (framed (sealIn v)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1) :
    u.mem x = (ctxW v s x).getD (s.mem x) := by
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
  unfold ctxW uW
  refine ctx_leavesL (fun hw => hz x hw) (fun hx => ?_) hx
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

/-- The unknowns `sealIn` ends with in `bodyCall`, entered from `s`. -/
noncomputable def uF (v : XorImpl) (s : State) : Nat → BitVec 64 := uW v (narrowF Spec.ChaCha20Poly1305.sealSig 8 s)

/-- What `bodyCall` leaves, entered from `s`: its callee's context, at
`rsp - 1720`, as `ctxL` says, through the release of the callee's frame, at
`rsp - 1744`. -/
noncomputable def ctxF (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  loseL (s.gpr .rsp - BitVec.ofNat 64 1744) 1728 (uF v s)
    (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1720) (s.gpr .r9).toNat)

theorem uF_agree (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.sealContract abi 1768).pub s₁ s₂) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (sealIn v), s₁.syms n = s₂.syms n) : uF v s₁ = uF v s₂ := by
  have k₁ : (Spec.ChaCha20Poly1305.sealSig.contract abi (Curry.const (fun _ => True) _)
      (Spec.ChaCha20Poly1305.sealPost abi.ptrBits) true (1752 + 8 + 8) none).pre s₁ := h₁
  have k₂ : (Spec.ChaCha20Poly1305.sealSig.contract abi (Curry.const (fun _ => True) _)
      (Spec.ChaCha20Poly1305.sealPost abi.ptrBits) true (1752 + 8 + 8) none).pre s₂ := h₂
  exact uW_agree v (narrowF_pre (bytes := 8) (by decide) (by decide) (by decide) (by decide)
      (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp) k₁)
    (narrowF_pre (bytes := 8) (by decide) (by decide) (by decide) (by decide)
      (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp) k₂)
    (narrowF_pub (bytes := 8) (by decide) (by decide) (by decide) k₁ k₂ hp)
    (by rw [narrowF_unknowns k₁ (by decide) (by decide) (by decide),
      narrowF_unknowns k₂ (by decide) (by decide) (by decide), hu])
    (by rw [narrowF_syms k₁ (by decide) (by decide) (by decide), narrowF_syms k₂ (by decide) (by decide) (by decide)]
        exact hsy)

/-- Through `forward`, from the entry: the context is at `rsp - 1720`. -/
theorem bodyCall_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s)
    (he : Exec isa (bodyCall v.callee v.poly) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1720)).Contains x 1) :
    u.mem x = (ctxF v s x).getD (s.mem x) := by
  have hs' : (Spec.ChaCha20Poly1305.sealSig.contract abi (Curry.const (fun _ => True) _)
      (Spec.ChaCha20Poly1305.sealPost abi.ptrBits) true (1752 + 8 + 8) none).pre s := hs
  have hb : body v.callee v.poly = framed (sealIn v) := rfl
  obtain ⟨hrsp, hg, -, -, hf⟩ := narrowF_facts (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8)
    (by decide) (by decide) (by decide) hs'
  have hC : (narrowF Spec.ChaCha20Poly1305.sealSig 8 s).gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24 =
      s.gpr .rsp - BitVec.ofNat 64 1720 := by
    rw [hrsp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub, BitVec.sub_sub, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add, sub_add_ofNat _ (by decide)]
  have hB : (narrowF Spec.ChaCha20Poly1305.sealSig 8 s).gpr .rsp - BitVec.ofNat 64 1728 =
      s.gpr .rsp - BitVec.ofNat 64 1744 := by
    rw [hrsp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub, BitVec.sub_sub, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
  have h := forward_leaves (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8) (stack := 1752)
    (name := bodyName true v.callee v.poly) (Shared.body_verified v) (P := fun s => (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s)
    (fun _ h => h)
    (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24))
    (L := fun s => ctxW v s)
    (fun s t u hs he => by rw [hb] at he; exact frameW_leaves v s t u hs he)
    (by decide) (by decide) (by decide) (by decide) (Shared.body_sp v) (Shared.body_depth v)
    (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp) hs' he x (by simp only [hC]; exact hx)
  rw [loseL_out (below_out (a := 1720) hx (by decide) (by decide))] at h
  simp only [ctxW, hB, hg .r9 (by decide) (by decide)] at h
  rw [show s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 24 = s.gpr .rsp - BitVec.ofNat 64 1720 from
    sub_add_ofNat _ (by decide)] at h
  unfold ctxF uF
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

/-- The state `seal`'s code for AVX-512 chooses its code in, after comparing
the length. -/
abbrev sB (v : XorImpl) (s : State) : State := afterB (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)) s

/-- What `seal` leaves below the stack pointer, run by run: its context as
`ctxW` or `ctxF` says, for the code the length chooses. -/
noncomputable def sealV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  if v.poly = .avx512 then
    if pSmall v (s.gpr .r9) then ctxF v.small (sB v s)
    else if v.callee.vl then ctxW v (sB v s) else ctxF v (sB v s)
  else ctxF v s

/-- The functions `bodyCall` calls indirectly: its code's. -/
theorem inames_bodyCall (v : XorImpl) {n : String} (h : n ∈ UpperLock.inames (sealIn v)) :
    n ∈ UpperLock.inames (bodyCall v.callee v.poly) := by
  simpa [UpperLock.inames, bodyCall, body, framed, Impl.ForwardCall.X86_64.forward,
    Impl.StackScratch.X86_64.withStackArgScratchWipedX, Impl.StackScratch.X86_64.withStackArgScratch] using h

theorem inames_framed {c : Prog isa} {n : String} (h : n ∈ UpperLock.inames c) :
    n ∈ UpperLock.inames (framed c) := by
  simpa [UpperLock.inames, framed, Impl.StackScratch.X86_64.withStackArgScratchWipedX,
    Impl.StackScratch.X86_64.withStackArgScratch] using h

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
      (La := fun s => ctxF v.small s)
      (Lc := fun s => if v.callee.vl then ctxW v s else ctxF v s)
      (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (fun _ _ hf hs => Shared.flags_pre true hf hs)
      (fun _ _ hf => by simp only [hf.gpr .rsp (by decide) (by decide)])
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

/-- What `ctxF` says depends only on what two runs agree on. -/
theorem ctxF_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.sealContract abi 1768).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (sealIn v), s₁.syms n = s₂.syms n) : ctxF v s₁ = ctxF v s₂ := by
  unfold ctxF; rw [uF_agree v h₁ h₂ hp hu hsy, hsp, h9]

theorem ctxW_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.sealContract abi 1752).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.sealContract abi 1752).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (sealIn v), s₁.syms n = s₂.syms n) : ctxW v s₁ = ctxW v s₂ := by
  unfold ctxW; rw [uW_agree v h₁ h₂ hp hu hsy, hsp, h9]

/-- What `sealV` says depends only on what two runs agree on: the stack
pointer, the length, and through `innerU` the public data, the unknowns and
the addresses of the functions the code calls indirectly. -/
theorem sealV_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.sealContract abi 1768).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.sealContract abi 1768).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (sealCode v.callee v.poly), s₁.syms n = s₂.syms n) :
    sealV v s₁ = sealV v s₂ := by
  by_cases hb : v.poly = .avx512
  · have hc : sealCode v.callee v.poly = .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (smallCall v.callee.small) (largeCode v.callee)) := by rw [hb]; rfl
    obtain ⟨f₁, u₁, y₁⟩ := afterB_facts (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s) s₁
    obtain ⟨f₂, u₂, y₂⟩ := afterB_facts (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s) s₂
    have q₁ := Shared.flags_pre true f₁ h₁
    have q₂ := Shared.flags_pre true f₂ h₂
    have qp := Shared.flags_pub true f₁ f₂ hp
    have qu : (sB v s₁).unknowns = (sB v s₂).unknowns := by rw [u₁, u₂, hu]
    have qsp : (sB v s₁).gpr .rsp = (sB v s₂).gpr .rsp := by
      rw [f₁.gpr .rsp (by decide) (by decide), f₂.gpr .rsp (by decide) (by decide), hsp]
    have q9 : (sB v s₁).gpr .r9 = (sB v s₂).gpr .r9 := by
      rw [f₁.gpr .r9 (by decide) (by decide), f₂.gpr .r9 (by decide) (by decide), h9]
    have qsy : ∀ c : Prog isa, (∀ n ∈ UpperLock.inames c, n ∈ UpperLock.inames (sealCode v.callee v.poly)) →
        ∀ n ∈ UpperLock.inames c, (sB v s₁).syms n = (sB v s₂).syms n := fun _ hc n hn => by
      rw [y₁, y₂]; exact hsy n (hc n hn)
    have hmem : ∀ c : Prog isa, ∀ n ∈ UpperLock.inames c, n ∈ UpperLock.inames (.seq
        (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl))) (Code.iteCold .b c (largeCode v.callee)) :
          Prog isa) := fun c n hn => by
      simp [UpperLock.inames, Code.iteCold, hn]
    have hmem' : ∀ c : Prog isa, ∀ n ∈ UpperLock.inames c, n ∈ UpperLock.inames (largeCode v.callee) →
        n ∈ UpperLock.inames (.seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
          (Code.iteCold .b (smallCall v.callee.small) (largeCode v.callee)) : Prog isa) := fun c n _ hn => by
      simp [UpperLock.inames, Code.iteCold, hn]
    simp only [sealV, hb, ↓reduceIte, h9]
    split
    · refine ctxF_pub v.small q₁ q₂ qp qsp q9 qu (qsy _ fun n hn => ?_)
      rw [hc]
      have := inames_bodyCall v.small hn
      rw [XorImpl.small_callee, v.small_poly] at this
      exact hmem _ n this
    · split
      · next hvl =>
        refine ctxW_pub v (Shared.pre_old true q₁) (Shared.pre_old true q₂) qp qsp q9 qu (qsy _ fun n hn => ?_)
        rw [hc]
        refine hmem' (sealIn v) n hn ?_
        unfold largeCode
        simp only [hvl, ↓reduceIte]
        have : sealIn v = «seal» v.callee .avx512 := by simp only [sealIn, hb, reduceCtorEq, ↓reduceIte]
        rw [← this]; exact inames_framed hn
      · next hvl =>
        refine ctxF_pub v q₁ q₂ qp qsp q9 qu (qsy _ fun n hn => ?_)
        rw [hc]
        refine hmem' (sealIn v) n hn ?_
        unfold largeCode
        simp only [hvl, Bool.false_eq_true, ↓reduceIte]
        have := inames_bodyCall v hn
        rwa [hb] at this
  · simp only [sealV, hb, ↓reduceIte]
    exact ctxF_pub v h₁ h₂ hp hsp h9 hu fun n hn => hsy n (by rw [sealCode_ne hb]; exact inames_bodyCall v hn)

/-- Two runs of `seal` leave the same bytes in their stack but the granules
`sealKs`: as `sealV` says. -/
theorem seal_resOk (v : XorImpl) :
    ResOk (sealCode v.callee v.poly) (Spec.ChaCha20Poly1305.sealContract abi 1768) 1768 sealKs (chunks 1768) := by
  unfold Spec.ChaCha20Poly1305.sealContract
  refine resOk_of_leaves (V := sealV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact sealCode_leaves v s t u hs he x (sealWindow hx hw)
  · intro s₁ s₂ h₁ h₂ hp ho hu hsy
    exact sealV_pub v h₁ h₂ hp (ho.2.2.1 .rsp (by decide)) (ho.2.2.1 .r9 (by decide)) hu hsy

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

/-- The unknowns `open`'s call ends with in its frame, entered from `s`. -/
noncomputable def uO (v : XorImpl) (s : State) : Nat → BitVec 64 :=
  innerU (openCall v.callee v.poly) (narrowS Spec.ChaCha20Poly1305.openSig .u64 212 1728 s)

/-- What `framed (openCall …)` leaves, entered from `s`: its context, at
`rsp - 1728 + 24`, as `ctxL` says, through the frame's release. -/
noncomputable def ctxO (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  loseL (s.gpr .rsp - BitVec.ofNat 64 1728) 1728 (uO v s)
    (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) (s.gpr .r9).toNat)

theorem ctxO_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (openCall v.callee v.poly), s₁.syms n = s₂.syms n) : ctxO v s₁ = ctxO v s₂ := by
  unfold ctxO uO
  rw [framed_innerU_agree (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64) (n := 212)
    (bytes := 1728) (stack := 56) (Shared.openCall_verified v) (by decide) (by decide) (by decide) (pre_local _ _)
    h₁ h₂ hp hu hsy (fun vs m₁ m₂ hl hb _ => Proof.ChaCha20Poly1305.openLeak_local 64 vs m₁ m₂ hl hb), hsp, h9]

/-- In its frame (`framed`): its context is at `rsp - 1728 + 24`, of which
the frame wipes the first 672 bytes. -/
theorem frameO_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s)
    (he : Exec isa (framed (openCall v.callee v.poly)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1) :
    u.mem x = (ctxO v s x).getD (s.mem x) := by
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
  unfold ctxO uO
  refine ctx_leavesL (fun hw => hz x hw) (fun hx => ?_) hx
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

/-- The state `open`'s code for IFMA chooses its code in. -/
abbrev sI (s : State) : State := afterB Stitch.ifmaTest s

/-- What `open` leaves below the stack pointer, run by run: its context as
`ctxO` says, for the code its length chooses. -/
noncomputable def openV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  if v.poly = .avx512 then
    if pSmall v (s.gpr .r9) then ctxO v.small (sB v s) else ctxO v (sB v s)
  else if v.poly = .ifma then
    if decide (Stitch.ifmaLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < Stitch.ifmaHi) then
      ctxO XorImpl.avx512vl.small (sI s)
    else ctxO v (sI s)
  else ctxO v s

theorem inames_ite {b : List Instr} {a c : Prog isa} {n : String}
    (h : n ∈ UpperLock.inames a ∨ n ∈ UpperLock.inames c) :
    n ∈ UpperLock.inames (.seq (.block b) (Code.iteCold .b a c) : Prog isa) := by
  rcases h with h | h <;> simp [UpperLock.inames, Code.iteCold, h]

/-- What `open` leaves in its context: as `openV` says. -/
theorem openCode_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s) (he : Exec isa (openCode v.callee v.poly) s t u)
    (x : Addr) (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24)).Contains x 1) :
    u.mem x = (openV v s x).getD (s.mem x) := by
  have hR : ∀ s u : State, Stitch.FlagsOnly s u →
      ctxR (u.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) =
        ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24) := fun _ _ hf => by
    simp only [hf.gpr .rsp (by decide) (by decide)]
  by_cases hb : v.poly = .avx512
  · have hc : openCode v.callee v.poly = .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (framed (openCall v.callee.small .avx2)) (framed (openCall v.callee .avx512))) := by
      rw [hb]; rfl
    rw [hc] at he
    have h := choose_leaves (P := fun s => (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s)
      (R := fun s => ctxR (s.gpr .rsp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 24))
      (La := fun s => ctxO v.small s) (Lc := fun s => ctxO v s)
      (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (fun _ _ hf hs => Shared.flags_pre false hf hs) hR
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
        (La := fun s => ctxO XorImpl.avx512vl.small s) (Lc := fun s => ctxO v s)
        (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
        (fun _ _ hf hs => Shared.flags_pre false hf hs) hR
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

/-- What `openV` says depends only on what two runs agree on. -/
theorem openV_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.openZeroContract abi 1784).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (openCode v.callee v.poly), s₁.syms n = s₂.syms n) :
    openV v s₁ = openV v s₂ := by
  -- After a comparison, from the code's states.
  have after : ∀ {b : List Instr} {p : Addr → Bool}
      (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ Stitch.FlagsOnly s u)
      (w : XorImpl) (c : Prog isa) (_ : c = openCall w.callee w.poly)
      (_ : ∀ n ∈ UpperLock.inames c, n ∈ UpperLock.inames (openCode v.callee v.poly)),
      ctxO w (afterB b s₁) = ctxO w (afterB b s₂) := by
    intro b p hb w c hc hcm
    obtain ⟨f₁, u₁, y₁⟩ := afterB_facts hb s₁
    obtain ⟨f₂, u₂, y₂⟩ := afterB_facts hb s₂
    refine ctxO_pub w (Shared.flags_pre false f₁ h₁) (Shared.flags_pre false f₂ h₂) (Shared.flags_pub false f₁ f₂ hp)
      (by rw [f₁.gpr .rsp (by decide) (by decide), f₂.gpr .rsp (by decide) (by decide), hsp])
      (by rw [f₁.gpr .r9 (by decide) (by decide), f₂.gpr .r9 (by decide) (by decide), h9])
      (by rw [u₁, u₂, hu]) fun n hn => ?_
    rw [y₁, y₂]; subst hc; exact hsy n (hcm n hn)
  by_cases hb : v.poly = .avx512
  · have hc : openCode v.callee v.poly = .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (framed (openCall v.callee.small .avx2)) (framed (openCall v.callee .avx512))) := by
      rw [hb]; rfl
    simp only [openV, hb, ↓reduceIte, h9]
    split
    · refine after (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s) v.small _ rfl fun n hn => ?_
      rw [XorImpl.small_callee, v.small_poly] at hn
      rw [hc]; exact inames_ite (.inl (inames_framed hn))
    · refine after (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s) v _ rfl fun n hn => ?_
      rw [hb] at hn
      rw [hc]; exact inames_ite (.inr (inames_framed hn))
  · by_cases hi : v.poly = .ifma
    · have hc : openCode v.callee v.poly = .seq (.block Stitch.ifmaTest)
          (Code.iteCold .b (framed (openCall Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2))
            (framed (openCall v.callee .ifma))) := by
        rw [hi]; rfl
      simp only [openV, hi, reduceCtorEq, ↓reduceIte, h9]
      split
      · refine after (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
          XorImpl.avx512vl.small _ rfl fun n hn => ?_
        rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hn
        rw [hc]; exact inames_ite (.inl (inames_framed hn))
      · refine after (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
          v _ rfl fun n hn => ?_
        rw [hi] at hn
        rw [hc]; exact inames_ite (.inr (inames_framed hn))
    · have hc : openCode v.callee v.poly = framed (openCall v.callee v.poly) := by
        revert hb hi
        generalize v.poly = b
        intro hb hi
        cases b <;> first | exact absurd rfl hb | exact absurd rfl hi | rfl
      simp only [openV, hb, hi, ↓reduceIte]
      exact ctxO_pub v h₁ h₂ hp hsp h9 hu fun n hn => hsy n (by rw [hc]; exact inames_framed hn)

theorem open_resOk (v : XorImpl) :
    ResOk (openCode v.callee v.poly) (Spec.ChaCha20Poly1305.openZeroContract abi 1784) 1784 openKs
      (chunks 1784) := by
  unfold Spec.ChaCha20Poly1305.openZeroContract
  refine resOk_of_leaves (V := openV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact openCode_leaves v s t u hs he x (openWindow hx hw)
  · intro s₁ s₂ h₁ h₂ hp ho hu hsy
    exact openV_pub v h₁ h₂ hp (ho.2.2.1 .rsp (by decide)) (ho.2.2.1 .r9 (by decide)) hu hsy

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

/-- The unknowns `open_to`'s code ends with in its frame, entered from `s`. -/
noncomputable def uT (v : XorImpl) (s : State) : Nat → BitVec 64 :=
  innerU (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly)
    (narrowS Spec.ChaCha20Poly1305.openToSig .u64 212 1744 s)

/-- What `open_to`'s code leaves in its frame, entered from `s`: its context,
at `rsp - 1744 + 40`, as `ctxL` says, through the frame's release. -/
noncomputable def ctxT (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  loseL (s.gpr .rsp - BitVec.ofNat 64 1744) 1744 (uT v s)
    (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40) (s.gpr .r9).toNat)

theorem ctxT_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.openToContract abi 1800).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly), s₁.syms n = s₂.syms n) :
    ctxT v s₁ = ctxT v s₂ := by
  unfold ctxT uT
  rw [framed_innerU_agree (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64) (n := 212)
    (bytes := 1744) (stack := 56) (OpenTo.body_verified v) (by decide) (by decide) (by decide) (openToPre_local _)
    h₁ h₂ hp hu hsy (Proof.ChaCha20Poly1305.openToLeak_local 64).toL, hsp, h9]

theorem inames_scratched {c : Prog isa} {n : String} (h : n ∈ UpperLock.inames c) :
    n ∈ UpperLock.inames (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched c) := by
  simpa [UpperLock.inames, Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched,
    Impl.StackScratch.X86_64.withStackArgScratchWipedX, Impl.StackScratch.X86_64.withStackArgScratch] using h

/-- In its frame (`OpenTo.scratched`): its context is at `rsp - 1744 + 40`,
of which the frame wipes the first 672 bytes. -/
theorem frameT_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State)
    (hs : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s)
    (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
      (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1744 + BitVec.ofNat 64 40)).Contains x 1) :
    u.mem x = (ctxT v s x).getD (s.mem x) := by
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
  unfold ctxT uT
  refine ctx_leavesL (fun hw => hz x hw) (fun hx => ?_) hx
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
noncomputable def openToV (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  if v.poly = .avx512 then
    if pSmall v (s.gpr .r9) then ctxT v.small (sB v s) else ctxT v (sB v s)
  else if v.poly = .ifma then
    if decide (Stitch.ifmaLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < Stitch.ifmaHi) then
      ctxT XorImpl.avx512vl.small (sI s)
    else ctxT v (sI s)
  else ctxT v s

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
      (La := fun s => ctxT v.small s) (Lc := fun s => ctxT v s)
      (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s)
      (fun _ _ hf hs => openTo_flags hf hs) hR
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
        (La := fun s => ctxT XorImpl.avx512vl.small s) (Lc := fun s => ctxT v s)
        (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
        (fun _ _ hf hs => openTo_flags hf hs) hR
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

/-- What `openToV` says depends only on what two runs agree on. -/
theorem openToV_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s₁)
    (h₂ : (Spec.ChaCha20Poly1305.openToContract abi 1800).pre s₂)
    (hp : (Spec.ChaCha20Poly1305.openToContract abi 1800).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (h9 : s₁.gpr .r9 = s₂.gpr .r9) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly),
      s₁.syms n = s₂.syms n) :
    openToV v s₁ = openToV v s₂ := by
  have after : ∀ {b : List Instr} {p : Addr → Bool}
      (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ Stitch.FlagsOnly s u)
      (w : XorImpl) (c : Prog isa) (_ : c = Impl.ChaCha20Poly1305.X86_64.OpenTo.body w.callee w.poly)
      (_ : ∀ n ∈ UpperLock.inames c,
        n ∈ UpperLock.inames (Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly)),
      ctxT w (afterB b s₁) = ctxT w (afterB b s₂) := by
    intro b p hb w c hc hcm
    obtain ⟨f₁, u₁, y₁⟩ := afterB_facts hb s₁
    obtain ⟨f₂, u₂, y₂⟩ := afterB_facts hb s₂
    refine ctxT_pub w (openTo_flags f₁ h₁) (openTo_flags f₂ h₂)
      (Shared.flags_pub_sig (sig := Spec.ChaCha20Poly1305.openToSig)
        (pre := Spec.ChaCha20Poly1305.openToPre 64) (post := Spec.ChaCha20Poly1305.openToPost 64) (wa := true)
        (stack := 1800) (leak := some (Spec.ChaCha20Poly1305.openToLeak 64)) (by decide) f₁ f₂ hp)
      (by rw [f₁.gpr .rsp (by decide) (by decide), f₂.gpr .rsp (by decide) (by decide), hsp])
      (by rw [f₁.gpr .r9 (by decide) (by decide), f₂.gpr .r9 (by decide) (by decide), h9])
      (by rw [u₁, u₂, hu]) fun n hn => ?_
    rw [y₁, y₂]; subst hc; exact hsy n (hcm n hn)
  by_cases hb : v.poly = .avx512
  · have hc : Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly =
        .seq (.block (Stitch.smallTest (Stitch.smallLim v.callee.small.vl)))
        (Code.iteCold .b (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee.small .avx2))
          (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee .avx512))) := by
      rw [hb]; rfl
    simp only [openToV, hb, ↓reduceIte, h9]
    split
    · refine after (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s) v.small _ rfl fun n hn => ?_
      rw [XorImpl.small_callee, v.small_poly] at hn
      rw [hc]; exact inames_ite (.inl (inames_scratched hn))
    · refine after (p := pSmall v) (fun s => Stitch.cmpSmall_ok v.callee.small.vl s) v _ rfl fun n hn => ?_
      rw [hb] at hn
      rw [hc]; exact inames_ite (.inr (inames_scratched hn))
  · by_cases hi : v.poly = .ifma
    · have hc : Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly = .seq (.block Stitch.ifmaTest)
          (Code.iteCold .b (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
              (Impl.ChaCha20Poly1305.X86_64.OpenTo.body Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2))
            (Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched
              (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee .ifma))) := by
        rw [hi]; rfl
      simp only [openToV, hi, reduceCtorEq, ↓reduceIte, h9]
      split
      · refine after (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
          XorImpl.avx512vl.small _ rfl fun n hn => ?_
        rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hn
        rw [hc]; exact inames_ite (.inl (inames_scratched hn))
      · refine after (p := fun n => decide (Stitch.ifmaLo ≤ n.toNat ∧ n.toNat < Stitch.ifmaHi)) Stitch.cmpWin_ok
          v _ rfl fun n hn => ?_
        rw [hi] at hn
        rw [hc]; exact inames_ite (.inr (inames_scratched hn))
    · have hc : Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly =
          Impl.ChaCha20Poly1305.X86_64.OpenTo.scratched (Impl.ChaCha20Poly1305.X86_64.OpenTo.body v.callee v.poly) := by
        revert hb hi
        generalize v.poly = b
        intro hb hi
        cases b <;> first | exact absurd rfl hb | exact absurd rfl hi | rfl
      simp only [openToV, hb, hi, ↓reduceIte]
      exact ctxT_pub v h₁ h₂ hp hsp h9 hu fun n hn => hsy n (by rw [hc]; exact inames_scratched hn)

theorem openTo_resOk (v : XorImpl) :
    ResOk (Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly)
      (Spec.ChaCha20Poly1305.openToContract abi 1800) 1800 openToKs (chunks 1800) := by
  unfold Spec.ChaCha20Poly1305.openToContract
  refine resOk_of_leaves (V := openToV v) ScrubAbi.plain ?_ ?_
  · intro s t u hs he x hx hw
    exact openToCode_leaves v s t u hs he x (openToWindow hx hw)
  · intro s₁ s₂ h₁ h₂ hp ho hu hsy
    exact openToV_pub v h₁ h₂ hp (ho.2.2.1 .rsp (by decide)) (ho.2.2.1 .r9 (by decide)) hu hsy

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
  ∀ x, (sR (s.gpr .rsp)).Contains x 1 → m x = (sealV v s x).getD (s.mem x)

/-- `seal_gather`'s callee `seal`, with what it leaves (`sealCode_leaves`). -/
def sealFnL (v : XorImpl) : Gather.Whole.SealFn :=
  { Gather.Whole.sealFn v with
    E := sealE v
    exec := fun s h => by
      obtain ⟨t, s', e, a, p⟩ := (Shared.seal_verified v).1 s h
      refine ⟨t, s', e, a, p, fun x hx => ?_⟩
      change Exec isa (sealCode v.callee v.poly) s t s' at e
      exact sealCode_leaves v s t s' h e x hx }

open Gather.Whole in
/-- `seal_gather` gathering the whole data before its call of `seal` leaves
`sR` of its callee's stack, at `rsp - 64`, as `sealV` says from the state its
callee starts in, called from a state with the entry's unknowns and
addresses of statics. -/
theorem gatherW_leaves (v : XorImpl) (s : State) (t : List Leak) (u : State) (hp : Gather.Whole.gatherPre s)
    (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole (Gather.width v)
      (sealFnL v).name (sealFnL v).code) s t u)
    (x : Addr) (hx : (sR (s.gpr .rsp - BitVec.ofNat 64 64)).Contains x 1) :
    ∃ c, Gather.Whole.Ready s c ∧ c.unknowns = s.unknowns ∧ c.syms = s.syms ∧
      u.mem x = (sealV v (Gather.Whole.xS s c) x).getD (s.mem x) := by
  have h := lay hp
  obtain ⟨t', u', he', c, m, hc, hcu, hcy, hE, hfr⟩ := sealGather_wpE (Gather.width v) (sealFnL v) hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  have hsp : (xS s c).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 64 := by
    rw [hc.xsp]; exact sub_add_ofNat _ (show 1768 ≤ 1832 by decide)
  have hE' := hE x (by rw [hsp]; exact hx)
  refine ⟨c, hc, hcu, hcy, ?_⟩
  -- The callee's memory on entry: ours, with the pushes and the slices gathered elsewhere.
  have hBs : s.gpr .rsp - BitVec.ofNat 64 64 - BitVec.ofNat 64 1704 = Bs s + BitVec.ofNat 64 64 := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]; exact (sub_add_ofNat _ (show 64 ≤ 1832 by decide)).symm
  have hxB := (Offset.lt_iff x (Bs s) (d := 64) (n := 1680) (by decide)).1 (by
    simp only [Region.Contains] at hx; rw [hBs] at hx; omega_using [hx])
  have hBn := h.hBn
  have nb : ∀ {d n : Nat}, (d + n ≤ 64 ∨ 1744 ≤ d) → d + n ≤ 1864 →
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
  -- The frames released after the call are apart from `sR`.
  have x₅ : u.mem x = m x := hfr x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact nb (by decide) (by decide)
    · exact nb (by decide) (by decide)
  rw [x₅, hE', x₁, x₂, hc.mem, x₄, x₃]

/-- `seal_split`'s code, of the instances with the AVX-512 implementations of
`vg_poly1305_blocks`, leaves the keystream area of `work` as `ksL` says. -/
theorem splitIn_leaves (v : XorImpl) (hv : v.poly = .avx512 ∨ v.poly = .ifma) (s : State) (t : List Leak)
    (u : State) (hs : (sealSplitScratchContract X86_64.abi 212 64).pre s)
    (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly) s t u) (x : Addr)
    (hx : (ksR (Split.eW s)).Contains x 1) :
    u.mem x = (ksL v (Split.eW s) (Split.eLn s) x).getD (s.mem x) := by
  have hf : Split.FPre s := Split.split_implies.pre s hs
  have hw : WP isa (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly) s fun z =>
      KsLeftZ v (Split.eW s) (Split.eLn s) s.mem z.mem := by
    rcases hv with hb | hb
    · have h := Split.split_wpK v .avx512 hb (.inl rfl) hf
      rw [hb]; exact h
    · have h := Split.split_wpK v .ifma hb (.inr rfl) hf
      rw [hb]; exact h
  obtain ⟨t', u', he', k⟩ := hw
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact ksLeftAt_leaves k hx

/-- The unknowns `seal_split`'s code ends with in its frame, entered from `s`. -/
noncomputable def uS (v : XorImpl) (s : State) : Nat → BitVec 64 :=
  innerU (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
    (narrowS Proof.ChaCha20Poly1305.sealSplitSig .u64 212 1736 s)

/-- What `seal_split` leaves in its frame, entered from `s`: its context, at
`rsp - 1736 + 40`, as `ctxL` says, through the frame's release. -/
noncomputable def ctxS (v : XorImpl) (s : State) : Addr → Option (BitVec 8) :=
  loseL (s.gpr .rsp - BitVec.ofNat 64 1736) 1736 (uS v s)
    (ctxL v (s.gpr .rsp - BitVec.ofNat 64 1736 + BitVec.ofNat 64 40) (stackArg s 1).toNat)

/-- In its frame of 1736 bytes, wiped after the code: its context is at
`rsp - 1736 + 40`. -/
theorem splitFrame_leaves (v : XorImpl) (hv : v.poly = .avx512 ∨ v.poly = .ifma) (s : State) (t : List Leak)
    (u : State) (hs : (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pre s)
    (he : Exec isa (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42
      (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)) s t u) (x : Addr)
    (hx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1736 + BitVec.ofNat 64 40)).Contains x 1) :
    u.mem x = (ctxS v s x).getD (s.mem x) := by
  have hs' : (Proof.ChaCha20Poly1305.sealSplitSig.contract abi (Proof.ChaCha20Poly1305.sealSplitPre abi.ptrBits)
      (Proof.ChaCha20Poly1305.sealSplitPost abi.ptrBits) true (64 + 1736) none).pre s := hs
  obtain ⟨-, ha, hl, hf⟩ := narrowS_args (sig := Proof.ChaCha20Poly1305.sealSplitSig) (e := .u64) (n := 212)
    (by decide) (by decide) (by decide) hs'
  have n3 : nStack Proof.ChaCha20Poly1305.sealSplitSig = 3 := by decide
  have hcx : Split.eW (narrowS Proof.ChaCha20Poly1305.sealSplitSig .u64 212 1736 s) =
      s.gpr .rsp - BitVec.ofNat 64 1736 + BitVec.ofNat 64 40 := by
    show stackArg _ 3 = _; rw [← n3]; exact hl
  have hL : Split.eLn (narrowS Proof.ChaCha20Poly1305.sealSplitSig .u64 212 1736 s) = (stackArg s 1).toNat := by
    show (stackArg _ 1).toNat = _; rw [ha 1 (by rw [n3]; decide)]
  obtain ⟨hz, hk⟩ := framedW_leaves (sig := Proof.ChaCha20Poly1305.sealSplitSig) (nm := "work") (e := .u64)
    (n := 212) (bytes := 1736) (stack := 64) (k := 42) (Split.sealSplit_verified v)
    (P := fun s => (sealSplitScratchContract X86_64.abi 212 64).pre s) (fun _ h => h)
    (R := fun s => ksR (Split.eW s)) (L := fun s => ksL v (Split.eW s) (Split.eLn s))
    (splitIn_leaves v hv) (by decide) (by decide) (by decide) (Split.sealSplitFor_spSafe v)
    (Split.sealSplitFor_xdepth v) (by decide) (sealSplitPre_local _) hs' he
  rw [n3, show 16 + 8 * 3 = 40 by decide] at hz hk
  unfold ctxS uS
  refine ctx_leavesL (fun hw => hz x hw) (fun hx => ?_) hx
  have h := hk x (by rw [hcx]; exact hx) (ks_not_wiped hx)
  rw [hcx, hL] at h
  rw [h]
  congr 1
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hx hc
  rw [Offset.add_add] at hx
  rw [n3, show (8 : Addr) = BitVec.ofNat 64 8 from rfl] at hc
  have h₁ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1736) (d := 40 + 672) (n := 1024) (by decide)).1
    (by omega_using [hx])
  have h₂ := (Offset.lt_iff x (s.gpr .rsp - BitVec.ofNat 64 1736) (d := 8) (n := 32) (by decide)).1
    (by omega_using [hc])
  omega_using [h₁, h₂]

/-- What `seal_split` leaves, as `seal_gather` needs it of its callee
(`SealSplitFn.E`). -/
def splitE (v : XorImpl) (s : State) (m : Mem) : Prop :=
  ∀ x, (ctxR (s.gpr .rsp - BitVec.ofNat 64 1736 + BitVec.ofNat 64 40)).Contains x 1 →
    m x = (ctxS v s x).getD (s.mem x)

/-- `seal_gather`'s callee `seal_split`, with what it leaves (`splitFrame_leaves`). -/
def sealSplitFnL (v : XorImpl) (hv : v.poly = .avx512 ∨ v.poly = .ifma) : Gather.SealSplitFn :=
  { Gather.sealSplitFn v with
    E := splitE v
    exec := fun s h => by
      obtain ⟨t, s', e, a, p⟩ := (Split.sealSplit_framed v).1 s h
      exact ⟨t, s', e, a, p, fun x hx => splitFrame_leaves v hv s t s' h e x hx⟩ }

/-- `seal_gather` calling `seal_split` leaves the part of its callee's context
in `sR (rsp - 64)` as `ctxL` says, with that context at `rsp - 1776`. -/
theorem gatherS_leaves (v : XorImpl) (hv : v.poly = .avx512 ∨ v.poly = .ifma) (s : State) (t : List Leak)
    (u : State) (hp : Gather.gatherPre s)
    (he : Exec isa (Impl.ChaCha20Poly1305.X86_64.SealGather.sealGather (Gather.width v)
      (sealSplitFnL v hv).name (sealSplitFnL v hv).code) s t u)
    (x : Addr) (hx : (sR (s.gpr .rsp - BitVec.ofNat 64 64)).Contains x 1) :
    ∃ c, Gather.Ready s c ∧ c.unknowns = s.unknowns ∧ c.syms = s.syms ∧
      u.mem x = (ctxS v (Gather.xS s c) x).getD (s.mem x) := by
  have h := Gather.lay hp
  obtain ⟨t', u', he', c, m, hc, hcu, hcy, hE, hfr⟩ := Gather.sealGather_wpE (Gather.width v) (sealSplitFnL v hv) hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  have hC : (Gather.xS s c).gpr .rsp - BitVec.ofNat 64 1736 + BitVec.ofNat 64 40 = s.gpr .rsp - BitVec.ofNat 64 1776 := by
    rw [hc.xsp, Gather.add_ofNat_sub_ofNat _ (show 1736 ≤ 1800 by decide), Offset.add_ofNat_add_ofNat]
    exact sub_add_ofNat _ (show 104 ≤ 1880 by decide)
  have hBs : s.gpr .rsp - BitVec.ofNat 64 64 - BitVec.ofNat 64 1704 = Gather.Bs s + BitVec.ofNat 64 112 := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]; exact (sub_add_ofNat _ (show 112 ≤ 1880 by decide)).symm
  have hxB := (Offset.lt_iff x (Gather.Bs s) (d := 112) (n := 1680) (by decide)).1 (by
    simp only [Region.Contains] at hx; rw [hBs] at hx; omega_using [hx])
  have hctx : (ctxR (s.gpr .rsp - BitVec.ofNat 64 1776)).Contains x 1 := by
    simp only [Region.Contains]
    rw [show s.gpr .rsp - BitVec.ofNat 64 1776 = Gather.Bs s + BitVec.ofNat 64 104 from
      (sub_add_ofNat _ (show 104 ≤ 1880 by decide)).symm]
    have := (Offset.lt_iff x (Gather.Bs s) (d := 104) (n := 1696) (by decide)).2 ⟨by omega_using [hxB], by omega_using [hxB]⟩
    omega_using [this]
  have hE' := hE x (by rw [hC]; exact hctx)
  refine ⟨c, hc, hcu, hcy, ?_⟩
  -- The callee's memory on entry: ours, with the pushes and the slices gathered elsewhere.
  have hBn := h.hBn
  have nb : ∀ {d n : Nat}, (d + n ≤ 112 ∨ 1792 ≤ d) → d + n ≤ 1880 →
      ¬ (⟨Gather.Bs s + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 := fun {d n} h₁ h₂ hc' => by
    simp only [Region.Contains] at hc'
    have := (Offset.lt_iff x (Gather.Bs s) (d := d) (n := n) (by omega_using [h₂])).1 (by omega_using [hc'])
    omega_using [h₁, this, hxB]
  have fx : Frame [⟨Gather.Bs s + BitVec.ofNat 64 1808, 24⟩, ⟨Gather.Bs s + BitVec.ofNat 64 1800, 8⟩]
      (Gather.gM s) (Gather.xS s c).mem := by
    rw [← hc.mem]
    exact ((hc.qmem h).1.mono (fun r hr => by simp at hr ⊢; exact Or.inl hr)).trans
      ((hc.xmem).mono (fun r hr => by simp at hr ⊢; exact Or.inr hr))
  have x₁ : (Gather.xS s c).mem x = Gather.gM s x := (fx x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact nb (by decide) (by decide)
    · exact nb (by decide) (by decide)).symm ▸ rfl
  have x₂ : Gather.gM s x = Gather.eM s x := h.frame_gM x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact bd x (by show (x - Gather.Bs s).toNat + 1 ≤ 1880; omega_using [hxB])
  have x₃ : Gather.eM s x = s.mem x := h.frame_eM x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact nb (by decide) (by decide)
  -- The frames released after the call are apart from `sR`.
  have x₅ : u.mem x = m x := hfr x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact nb (by decide) (by decide)
    · exact nb (by decide) (by decide)
  rw [x₅, hE', x₁, x₂, x₃]

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
`rsp` but those wholly in `sR (rsp - 64)`, `[112, 1792)` from their bottom:
the part of its callee's context that `seal`'s and `seal_split`'s layouts
share. -/
def gatherKs : List Nat := ksGran 1880 112 1792

theorem gatherWindow {R x : Addr} (hx : (⟨R - BitVec.ofNat 64 1880, 1880⟩ : Region).Contains x 1)
    (hw : ¬ WCov gatherKs (chunks 1880) R x) : (sR (R - BitVec.ofNat 64 64)).Contains x 1 := by
  have hm := ksWindow (by decide) (by decide) hx hw
  simp only [Region.Contains]
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, Offset.sub_ofNat_eq R (show 64 + 1704 ≤ 1880 by decide)]
  have := (Offset.lt_iff x (R - BitVec.ofNat 64 1880) (d := 1880 - (64 + 1704)) (n := 1680) (by decide)).2
    ⟨by omega_using [hm], by omega_using [hm]⟩
  omega_using [this]

theorem xSW_unknowns {s c : State} : (Gather.Whole.xS s c).unknowns = fun n => c.unknowns (n + 1) := by
  have e : (Gather.Whole.xS s c).unknowns = fun n => (Gather.Whole.qS c).unknowns (n + 1) := rfl
  rw [e]; simp only [Gather.Whole.qS, Gather.pushed_unknowns]

theorem xSW_syms {s c : State} : (Gather.Whole.xS s c).syms = c.syms := by
  have e : (Gather.Whole.xS s c).syms = (Gather.Whole.qS c).syms := rfl
  rw [e]; simp only [Gather.Whole.qS, Gather.pushed_syms]

theorem xS_unknowns {s c : State} : (Gather.xS s c).unknowns = fun n => c.unknowns (n + 1) := by
  have e : (Gather.xS s c).unknowns = fun n => (Gather.qS c).unknowns (n + 1) := rfl
  rw [e]; simp only [Gather.qS, Gather.pushed_unknowns]

theorem xS_syms {s c : State} : (Gather.xS s c).syms = c.syms := by
  have e : (Gather.xS s c).syms = (Gather.qS c).syms := rfl
  rw [e]; simp only [Gather.qS, Gather.pushed_syms]

/-- What `seal` leaves, called by `seal_gather` gathering the whole data, is
the same in two runs `seal_gather`'s contract relates, from states with the
same unknowns, calling it with the unknowns they were entered with. -/
theorem whole_agree (v : XorImpl) {f₁ f₂ c₁ c₂ : State} (p₁ : Gather.Whole.gatherPre f₁)
    (p₂ : Gather.Whole.gatherPre f₂) (hq : Gather.Whole.gatherPub f₁ f₂) (r₁ : Gather.Whole.Ready f₁ c₁)
    (r₂ : Gather.Whole.Ready f₂ c₂) (cu₁ : c₁.unknowns = f₁.unknowns) (cu₂ : c₂.unknowns = f₂.unknowns)
    (cy₁ : c₁.syms = f₁.syms) (cy₂ : c₂.syms = f₂.syms) (hu : f₁.unknowns = f₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (sealCode v.callee v.poly), f₁.syms n = f₂.syms n) :
    sealV v (Gather.Whole.xS f₁ c₁) = sealV v (Gather.Whole.xS f₂ c₂) := by
  obtain ⟨-, -, hB, -, -, -, -, -, hl, -, -⟩ := Gather.Whole.pub_facts hq
  refine sealV_pub v (Gather.Whole.sealSpec_pre (r₁.call (Gather.Whole.lay p₁)).1)
    (Gather.Whole.sealSpec_pre (r₂.call (Gather.Whole.lay p₂)).1) (Gather.Whole.callee_pub_of p₁ p₂ hq r₁ r₂)
    (by rw [r₁.xsp, r₂.xsp, hB])
    (by rw [Gather.Whole.xgpr_eq (by decide), Gather.Whole.xgpr_eq (by decide), r₁.r9, r₂.r9, hl])
    (by rw [xSW_unknowns, xSW_unknowns, cu₁, cu₂, hu]) fun n hn => ?_
  rw [xSW_syms, xSW_syms, cy₁, cy₂]; exact hsy n hn

/-- What `seal_split`'s frame leaves is the same in two runs its contract
relates with the same stack pointer, length and unknowns. -/
theorem ctxS_pub (v : XorImpl) {s₁ s₂ : State} (h₁ : (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pre s₁)
    (h₂ : (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pre s₂)
    (hp : (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pub s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (ha : stackArg s₁ 1 = stackArg s₂ 1) (hu : s₁.unknowns = s₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly),
      s₁.syms n = s₂.syms n) : ctxS v s₁ = ctxS v s₂ := by
  unfold ctxS uS
  rw [framed_innerU_agree (sig := Proof.ChaCha20Poly1305.sealSplitSig) (nm := "work") (e := .u64) (n := 212)
    (bytes := 1736) (stack := 64) (Split.sealSplit_verified v) (by decide) (by decide) (by decide)
    (sealSplitPre_local _) h₁ h₂ hp hu hsy, hsp, ha]

/-- What `seal_split` leaves, called by `seal_gather`, is the same in two runs
`seal_gather`'s contract relates, as `whole_agree`. -/
theorem split_agree (v : XorImpl) {f₁ f₂ c₁ c₂ : State} (p₁ : Gather.gatherPre f₁) (p₂ : Gather.gatherPre f₂)
    (hq : Gather.gatherPub f₁ f₂) (r₁ : Gather.Ready f₁ c₁) (r₂ : Gather.Ready f₂ c₂)
    (cu₁ : c₁.unknowns = f₁.unknowns) (cu₂ : c₂.unknowns = f₂.unknowns)
    (cy₁ : c₁.syms = f₁.syms) (cy₂ : c₂.syms = f₂.syms) (hu : f₁.unknowns = f₂.unknowns)
    (hsy : ∀ n ∈ UpperLock.inames (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly),
      f₁.syms n = f₂.syms n) :
    ctxS v (Gather.xS f₁ c₁) = ctxS v (Gather.xS f₂ c₂) := by
  obtain ⟨-, -, hB, -, -, -, -, -, -, -, hl, -, -⟩ := Gather.pub_facts p₁ p₂ hq
  refine ctxS_pub v (Gather.sealSplitSpec_pre (r₁.call (Gather.lay p₁)).1)
    (Gather.sealSplitSpec_pre (r₂.call (Gather.lay p₂)).1) (Gather.callee_pub_of p₁ p₂ hq r₁ r₂)
    (by rw [r₁.xsp, r₂.xsp, hB]) (by rw [r₁.xa1 (Gather.lay p₁), r₂.xa1 (Gather.lay p₂), hl])
    (by rw [xS_unknowns, xS_unknowns, cu₁, cu₂, hu]) fun n hn => ?_
  rw [xS_syms, xS_syms, cy₁, cy₂]; exact hsy n hn

/-- Two runs of `seal_gather` leave the same bytes in their stack but the
granules `gatherKs`: what its callee leaves in `sR (rsp - 64)` depends only
on what they agree on (`whole_agree`, `split_agree`). -/
theorem gather_resOk (v : XorImpl) :
    ResOk (Gather.gatherCode v) (Spec.ChaCha20Poly1305.sealGatherContract abi 1880) 1880 gatherKs
      (chunks 1880) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx hw
  have hx₁ := gatherWindow hx hw
  have hsp : s₂.gpr .rsp = s₁.gpr .rsp := (ho.2.2.1 .rsp (by decide)).symm
  have hx₂ : (sR (s₂.gpr .rsp - BitVec.ofNat 64 64)).Contains x 1 := by rw [hsp]; exact hx₁
  -- The bytes the callee leaves as it found them were the same on entry, outside the buffers.
  have hout : s₁.mem x = s₂.mem x := by
    have h₁' : (Spec.ChaCha20Poly1305.sealGatherSig.contract abi (Spec.ChaCha20Poly1305.sealGatherPre abi.ptrBits)
        (Spec.ChaCha20Poly1305.sealGatherPost abi.ptrBits) false 1880 none).pre s₁ := h₁
    refine ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x fun r hr => ?_
    exact (contract_pre_scrub ScrubAbi.plain h₁').2 r hr |>.2 (by decide) x hx
  have fin : ∀ {V₁ V₂ : Addr → Option (BitVec 8)}, V₁ = V₂ → u₁.mem x = (V₁ x).getD (s₁.mem x) →
      u₂.mem x = (V₂ x).getD (s₂.mem x) → u₁.mem x = u₂.mem x := fun hV a b => by rw [a, b, hV, hout]
  have p₁ : Gather.gatherPre s₁ := Gather.gather_implies.pre s₁ h₁
  have p₂ : Gather.gatherPre s₂ := Gather.gather_implies.pre s₂ h₂
  have hq : Gather.gatherPub s₁ s₂ := Gather.gather_implies.pub s₁ s₂ h₁ h₂ hp
  have same (s : State) : Gather.CmpSame s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  -- The whole data gathered, from states after a comparison that keeps the unknowns.
  have whole : ∀ {f₁ f₂ : State} {t₁ t₂ : List Leak}, Gather.CmpSame s₁ f₁ → Gather.CmpSame s₂ f₂ →
      f₁.unknowns = f₂.unknowns → f₁.syms = s₁.syms → f₂.syms = s₂.syms →
      (∀ n ∈ UpperLock.inames (sealCode v.callee v.poly), s₁.syms n = s₂.syms n) →
      Exec isa (Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole (Gather.width v) (sealFnL v).name
        (sealFnL v).code) f₁ t₁ u₁ →
      Exec isa (Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole (Gather.width v) (sealFnL v).name
        (sealFnL v).code) f₂ t₂ u₂ → u₁.mem x = u₂.mem x := by
    intro f₁ f₂ t₁ t₂ hf₁ hf₂ fu fy₁ fy₂ hs th₁ th₂
    have wp₁ := Gather.whole_pre hf₁ p₁
    have wp₂ := Gather.whole_pre hf₂ p₂
    obtain ⟨c₁, r₁, cu₁, cy₁, m₁⟩ := gatherW_leaves v f₁ _ u₁ wp₁ th₁ x
      (by rw [hf₁.gpr .rsp (by decide)]; exact hx₁)
    obtain ⟨c₂, r₂, cu₂, cy₂, m₂⟩ := gatherW_leaves v f₂ _ u₂ wp₂ th₂ x
      (by rw [hf₂.gpr .rsp (by decide)]; exact hx₂)
    rw [hf₁.mem] at m₁
    rw [hf₂.mem] at m₂
    exact fin (whole_agree v wp₁ wp₂ (Gather.whole_pub hf₁ hf₂ hq) r₁ r₂ cu₁ cu₂ cy₁ cy₂ fu
      fun n hn => by rw [fy₁, fy₂]; exact hs n hn) m₁ m₂
  by_cases hb : v.poly = .avx512 ∨ v.poly = .ifma
  · have hgc : Gather.gatherCode v = Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherBy
        (Impl.ChaCha20Poly1305.X86_64.SealGather.byLim v.poly) (Gather.width v) (sealFnL v).name (sealFnL v).code
        (sealSplitFnL v hb).name (sealSplitFnL v hb).code := by
      unfold Gather.gatherCode; split
      · rfl
      · rfl
      · next h₁ h₂ => rcases hb with hb | hb
                      · exact absurd hb h₁
                      · exact absurd hb h₂
    rw [hgc] at e₁ e₂ hsy
    unfold Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherBy at e₁ e₂ hsy
    have hlim : Impl.ChaCha20Poly1305.X86_64.SealGather.byLim v.poly < 2 ^ 31 := by
      rcases Gather.byLim_cases v with h | h <;> rw [h] <;> decide
    obtain ⟨_, f₁, b₁, hq₁, hf₁⟩ := Gather.lenCmp_ok hlim s₁ (Gather.len_in p₁)
    obtain ⟨_, f₂, b₂, hq₂, hf₂⟩ := Gather.lenCmp_ok hlim s₂ (Gather.len_in p₂)
    have hL : Gather.L s₁ = Gather.L s₂ := by
      obtain ⟨-, -, -, -, -, -, -, -, -, a1, -, -⟩ := hq; exact congrArg BitVec.toNat a1
    obtain ⟨fu₁, fy₁⟩ : f₁.unknowns = s₁.unknowns ∧ f₁.syms = s₁.syms := by
      cases b₁ with | block h => exact ⟨(Scrub.execBlock_unknowns h h).2.1, execBlock_syms h⟩
    obtain ⟨fu₂, fy₂⟩ : f₂.unknowns = s₂.unknowns ∧ f₂.syms = s₂.syms := by
      cases b₂ with | block h => exact ⟨(Scrub.execBlock_unknowns h h).2.1, execBlock_syms h⟩
    have fu : f₁.unknowns = f₂.unknowns := by rw [fu₁, fu₂, hu]
    cases e₁ with
    | @seq _ _ _ g₁ _ _ _ k₁ l₁ =>
      cases e₂ with
      | @seq _ _ _ g₂ _ _ _ k₂ l₂ =>
        obtain rfl := (Exec.det k₁ b₁).2
        obtain rfl := (Exec.det k₂ b₂).2
        cases l₁ with
        | iteT v₁ th₁ =>
          cases l₂ with
          | iteT v₂ th₂ =>
            exact whole hf₁ hf₂ fu fy₁ fy₂ (fun n hn => hsy n (by simp [UpperLock.inames,
              Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole, sealFnL, Gather.Whole.sealFn, hn])) th₁ th₂
          | iteF v₂ _ =>
            rw [hq₁] at v₁; rw [hq₂, ← hL, v₁] at v₂; cases v₂
        | iteF v₁ el₁ =>
          cases l₂ with
          | iteT v₂ _ =>
            rw [hq₁] at v₁; rw [hq₂, ← hL, v₁] at v₂; cases v₂
          | iteF v₂ el₂ =>
            have pp₁ := Gather.pre_same hf₁ p₁
            have pp₂ := Gather.pre_same hf₂ p₂
            obtain ⟨c₁, r₁, cu₁, cy₁, m₁⟩ := gatherS_leaves v hb g₁ _ u₁ pp₁ el₁ x
              (by rw [hf₁.gpr .rsp (by decide)]; exact hx₁)
            obtain ⟨c₂, r₂, cu₂, cy₂, m₂⟩ := gatherS_leaves v hb g₂ _ u₂ pp₂ el₂ x
              (by rw [hf₂.gpr .rsp (by decide)]; exact hx₂)
            rw [hf₁.mem] at m₁
            rw [hf₂.mem] at m₂
            exact fin (split_agree v pp₁ pp₂ (Gather.pub_same hf₁ hf₂ hq) r₁ r₂ cu₁ cu₂ cy₁ cy₂ fu
              fun n hn => by
                rw [fy₁, fy₂]
                exact hsy n (by simp [UpperLock.inames, Impl.ChaCha20Poly1305.X86_64.SealGather.sealGather,
                  sealSplitFnL, Gather.sealSplitFn, Impl.StackScratch.X86_64.withStackArgScratchWipedX,
                  Impl.StackScratch.X86_64.withStackArgScratch, hn])) m₁ m₂
  · have hgc : Gather.gatherCode v = Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole (Gather.width v)
        (sealFnL v).name (sealFnL v).code := by
      unfold Gather.gatherCode; split
      · next h => exact absurd (.inl h) hb
      · next h => exact absurd (.inr h) hb
      · rfl
    rw [hgc] at e₁ e₂ hsy
    exact whole (same s₁) (same s₂) hu rfl rfl (fun n hn => hsy n (by simp [UpperLock.inames,
      Impl.ChaCha20Poly1305.X86_64.SealGather.sealGatherWhole, sealFnL, Gather.Whole.sealFn, hn])) e₁ e₂

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealGatherPost_out _)

def gatherPlain (v : XorImpl) : Registration Spec.ChaCha20Poly1305.sealGatherApi X86_64.target where
  suffix := v.suffix
  code := Gather.gatherCode v
  verified := Gather.gather_verified v
  spSafe := Gather.gather_spSafe v

/-- `seal_gather` of an instance, calling `seal`'s code unscrubbed (`…_core`),
followed by the clearing of all of its stack but its callee's context
(`gatherKs`). -/
def gatherReg (v : XorImpl) : Registration Spec.ChaCha20Poly1305.sealGatherApi X86_64.target :=
  RScrub.withScrubResM (gatherPlain v) (gatherOut _) gatherKs (gather_resOk v)

end VG.Proof.ChaCha20Poly1305.X86_64.Scrub
