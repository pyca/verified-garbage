module

public import VerifiedGarbage.Proof.HmacTable.AArch64
public import VerifiedGarbage.Impl.Hkdf.AArch64
public import VerifiedGarbage.Spec.Hkdf.Table
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.AArch64.Steps
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.Hkdf.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# HKDF on AArch64: `vg_hkdf_key`, correct

The contract the proof is written against (`keyR`), for the table `hmac` of
one variant `w` (`MdHash`), whose functions an indirect call of `f`'s
reaches: `key(prk, prk_len, key, hmac)` makes the 384 bytes at `key` hold
HMAC's states keyed with `PRK` (`Spec.Hkdf.Keyed`, with `w`'s streaming
states). The return address pushed and the frame (`kFr` bytes, the working
space) allocated, `keyArgs` moves `init`'s arguments into place and its
address into `x16` (`args_ok`); HMAC's `init` for a key of any length,
through the table, writes the states, and the frame's release and the pop
leave them as they are (`key_correct`).

Where the stack is: `kStack` bytes below the stack pointer on entry, from
`B` (`base`) up: the 16 bytes the call of `init` uses, the frame, and the
return address pushed (`StackAt`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.AArch64

open VG VG.AArch64 VG.AArch64.Steps
open VG.Impl.Hkdf.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (TabOK TabMem)

/-- What the functions need of a variant's sizes: its streaming states fit
their 192 bytes, and the working space of its functions the frames'. -/
structure HOk (w : MdHash) : Prop where
  hS : w.H.S ≤ 192
  hA : 8 * (w.H.W + w.H.S) ≤ work
  hW : 8 * w.H.W ≤ 1872
  hWb : w.ok.stream.Wb ≤ 1872

instance (w : MdHash) : Decidable (HOk w) :=
  decidable_of_iff (w.H.S ≤ 192 ∧ 8 * (w.H.W + w.H.S) ≤ work ∧ 8 * w.H.W ≤ 1872 ∧ w.ok.stream.Wb ≤ 1872)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-! ## The stack -/

/-- The return address pushed, a frame of `fr` bytes, and the 16 bytes below
it that the calls use: `B` is the stack's lowest byte. -/
structure StackAt (s : State) (fr : Nat) (B : Addr) : Prop where
  sp : s.sp = B + BitVec.ofNat 64 (fr + 32)
  push : s.sp - 16 = B + BitVec.ofNat 64 (fr + 16)
  frame : s.sp - 16 - BitVec.ofNat 64 fr = B + BitVec.ofNat 64 16
  nw : B.toNat + (fr + 32) ≤ 2 ^ 64

/-- The stack's lowest byte, `fr + 32` bytes below the stack pointer. -/
abbrev base (s : State) (fr : Nat) : Addr := s.sp - BitVec.ofNat 64 (fr + 32)

theorem stackAt (s : State) (fr : Nat) (h : fr + 32 ≤ s.sp.toNat) : StackAt s fr (base s fr) := by
  have e : ∀ a b : Nat, a ≤ fr + 32 → b = fr + 32 - a →
      s.sp - BitVec.ofNat 64 a = base s fr + BitVec.ofNat 64 b := fun a b ha hb => by
    rw [Offset.sub_ofNat_eq s.sp ha, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show s.sp = s.sp - BitVec.ofNat 64 0 from (BitVec.sub_zero _).symm, e 0 (fr + 32) (by omega_using [])
      (by omega_using [])]
  · exact e 16 (fr + 16) (by omega_using []) (by omega_using [])
  · rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.sub_sub_ofNat]
    exact e (16 + fr) 16 (by omega_using []) (by omega_using [])
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, s.sp.isLt])]; exact h),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, s.sp.isLt])]
    omega_using [h]

/-! ## `vg_hkdf_key` -/

/-- The stack `vg_hkdf_key` uses: the return address, its frame, and the 16
bytes below it that the call of `init` uses. -/
def kStack : Nat := kFr + 32

theorem kFr_eq : kFr = 3408 := rfl
theorem kStack_eq : kStack = 3440 := rfl

/-- `key(prk, prk_len, key, hmac)`, with `N` bytes of stack, for the table
`hmac` of `w`, whose functions an indirect call of `f`'s reaches, with the
addresses of the functions `ns` public. -/
def keyR (w : MdHash) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let prk : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let key : Region := ⟨s.gpr .x2, 384⟩
    let tab : Region := ⟨s.gpr .x3, 48⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 N, N⟩
    N ≤ s.sp.toNat ∧ s.rd = [prk, tab] ∧ s.wr = [key] ∧ prk.Disjoint key ∧ key.Disjoint tab ∧
      stk.Disjoint prk ∧ stk.Disjoint key ∧ stk.Disjoint tab ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 384 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 48 ≤ 2 ^ 64 ∧ TabMem w.H s.syms (s.gpr .x3) s.mem ∧ TabOK w.H f s.syms
  post s s' := Spec.Hkdf.Keyed w.ok.SH s'.mem (s.gpr .x2) (Spec.Sha256.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The state the frame's body starts in. -/
abbrev entered (fr : Nat) (s : State) : State := allocated fr (pushed .x30 s)

section
variable {w : MdHash} {f : Fns} {ns : List String}

/-- What `keyArgs` leaves: `init`'s arguments, and its address in `x16`. -/
structure KA (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x2
  x1 : t.gpr .x1 = s.gpr .x2 + BitVec.ofNat 64 192
  x2 : t.gpr .x2 = s.gpr .x0
  x3 : t.gpr .x3 = s.gpr .x1
  x4 : t.gpr .x4 = base s kFr + BitVec.ofNat 64 16
  x16 : t.gpr .x16 = s.syms w.H.hmacInitAnyN
  cs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = base s kFr + BitVec.ofNat 64 16
  mem : t.mem = (entered kFr s).mem
  rd : t.rd = s.rd
  wr : t.wr = (entered kFr s).wr
  syms : t.syms = s.syms

/-- The frame's state, from the contract's precondition. -/
theorem entered_facts {s : State} (hp : (keyR w f ns kStack).pre s) :
    StackAt s kFr (base s kFr) ∧ (entered kFr s).sp = base s kFr + BitVec.ofNat 64 16 ∧
      (entered kFr s).wr = ⟨base s kFr + BitVec.ofNat 64 16, kFr⟩ ::
        ⟨base s kFr + BitVec.ofNat 64 (kFr + 16), 16⟩ :: s.wr := by
  have hS := stackAt s kFr (by rw [← kStack]; exact hp.1)
  refine ⟨hS, hS.frame, ?_⟩
  show ⟨s.sp - 16 - BitVec.ofNat 64 kFr, kFr⟩ :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [hS.frame, hS.push]

theorem args_ok {s : State} (hp : (keyR w f ns kStack).pre s) :
    WP isa (.block keyArgs) (entered kFr s) (KA (w := w) s) := by
  obtain ⟨hS, hsp, hwr⟩ := entered_facts hp
  obtain ⟨-, hrd, -, -, -, -, -, st, -, -, -, tm, -⟩ := hp
  unfold keyArgs
  -- The table's word 0, apart from the return address the push wrote.
  have htab : (entered kFr s).mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 64 = s.syms w.H.hmacInitAnyN := by
    have hf : Frame [⟨s.sp - 16, 16⟩] s.mem (entered kFr s).mem :=
      (Frame.refl _ _).write (List.mem_singleton_self _) _
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
    rw [hf.readW (r := ⟨s.gpr .x3, 48⟩) (Offset.contains_base _ (by decide) (by decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hS.push]
        exact (st.symm.sub_right (by
          rw [show s.sp - BitVec.ofNat 64 kStack = base s kFr from rfl]
          exact Offset.sub_base _ (by omega_using [kStack_eq, kFr_eq])))) (by decide)]
    exact tm.1
  refine wp_ldr (ha := rfl) (by decide)
    ⟨⟨s.gpr .x3, 48⟩, List.mem_append_left _ (by show _ ∈ s.rd; rw [hrd]; simp),
      Offset.contains_base _ (by decide) (by decide)⟩ fun t₁ u₁ =>
    wp_addImm (by decide) fun t₂ u₂ => wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ =>
    wp_addImm (by decide) fun t₅ u₅ => wp_addImm (by decide) fun t₆ u₆ =>
    wp_addSp (by decide) fun t₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x16 → r ≠ .x3 → r ≠ .x9 → r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x4 →
      t₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    rw [u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2,
      u₁.other r h1]; rfl
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := BitVec.add_zero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
    exact BitVec.add_zero _
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; rfl
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
    rw [BitVec.add_zero, BitVec.add_zero]; rfl
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
    exact BitVec.add_zero _
  · rw [u₇.gpr, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hsp, e0]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact htab
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact g r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hsp]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]; rfl

theorem toNat_addN {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The stack region the contract gives, from its lowest byte. -/
theorem stk_eq (s : State) : s.sp - BitVec.ofNat 64 kStack = base s kFr := rfl

/-- `init`'s regions, from what `keyArgs` leaves. -/
theorem any_args {s t : State} (hw : HOk w) (hp : (keyR w f ns kStack).pre s) (ka : KA (w := w) s t) :
    Proof.Pbkdf2.Md.AArch64.Any.AnyArgs (H := w.H) t (s.gpr .x2) (s.gpr .x2 + BitVec.ofNat 64 192) (s.gpr .x0)
      (base s kFr + BitVec.ofNat 64 16) (s.gpr .x1).toNat := by
  obtain ⟨hS, -, hwrE⟩ := entered_facts hp
  obtain ⟨-, hrd, hwr, pk, -, sp', sk, -, np, nk, -, -, -⟩ := hp
  have hS192 := hw.hS; have hA := hw.hA
  have hw' : work = 3408 := rfl
  have hnw := hS.nw
  rw [stk_eq] at sp' sk
  have hsc : Region.Sub ⟨base s kFr + BitVec.ofNat 64 16, 8 * (w.H.W + w.H.S)⟩ ⟨base s kFr, kStack⟩ :=
    Offset.sub_base _ (by omega_using [hA, hw', kStack_eq])
  have hlow : below t.sp 16 = ⟨base s kFr, 16⟩ := by
    show (⟨t.sp - BitVec.ofNat 64 16, 16⟩ : Region) = _
    rw [ka.sp, BitVec.add_sub_cancel]
  have hlowS : Region.Sub ⟨base s kFr, 16⟩ ⟨base s kFr, kStack⟩ := Region.sub_prefix (by omega_using [kStack_eq])
  have hkS : Region.Sub ⟨s.gpr .x2, w.H.S⟩ ⟨s.gpr .x2, 384⟩ := Region.sub_prefix (by omega_using [hS192])
  have hoS : Region.Sub ⟨s.gpr .x2 + BitVec.ofNat 64 192, w.H.S⟩ ⟨s.gpr .x2, 384⟩ :=
    Offset.sub_base _ (by omega_using [hS192])
  have hB : (base s kFr).toNat + kStack ≤ 2 ^ 64 := hnw
  refine ⟨ka.x0, ka.x1, ka.x2, by rw [ka.x3], ka.x4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact VG.Covers.left (by rw [ka.rd, hrd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
  · rw [ka.wr, hwrE, hwr]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨s.gpr .x2, 384⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; omega_using [hS192]⟩
    · exact ⟨⟨s.gpr .x2, 384⟩, by simp, 192, rfl, by dsimp only; omega_using [hS192]⟩
    · exact ⟨⟨base s kFr + BitVec.ofNat 64 16, kFr⟩, by simp, 0, (BitVec.add_zero _).symm,
        by dsimp only; omega_using [hA, hw', kFr_eq]⟩
  · exact Offset.base_disjoint (s.gpr .x2) (e := 192) (n := w.H.S) (k := w.H.S) (by omega_using [hS192])
      (by omega_using [hS192])
  · exact (sk.symm.sub_left hkS).sub_right hsc
  · exact (sk.symm.sub_left hoS).sub_right hsc
  · exact pk.sub_right hkS
  · exact pk.sub_right hoS
  · exact sp'.symm.sub_right hsc
  · rw [ka.sp, toNat_addN (by omega_using [hB, kStack_eq])]; omega_using []
  · rw [hlow]; exact (sk.sub_left hlowS).sub_right hkS
  · rw [hlow]; exact (sk.sub_left hlowS).sub_right hoS
  · rw [hlow]; exact sp'.sub_left hlowS
  · rw [hlow]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hA, hw', hB, kStack_eq])
  · rw [toNat_addN (by omega_using [hB, kStack_eq])]
    omega_using [hA, hw', hB, kStack_eq]

/-- A state at `p` represents the same message in memory that agrees with it
there. -/
theorem repr_keep {m m' : Mem} {p : Addr} {msg : List Byte}
    (h : ∀ i < w.H.S, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) (hr : w.ok.SH.Repr m p msg) :
    w.ok.SH.Repr m' p msg :=
  w.ok.stream.repr _ _ _ _ _ h hr

/-- `vg_hkdf_key`: the return address pushed, its frame, the arguments, and
HMAC's `init` through the table. -/
theorem key_correct {s : State} (hw : HOk w) (hp : (keyR w f ns kStack).pre s) :
    WP isa (key f) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (keyR w f ns kStack).post s s' := by
  obtain ⟨hS, hsp, hwr⟩ := entered_facts hp
  have hN := hp.1
  have hS192 := hw.hS; have hA := hw.hA
  have hw' : work = 3408 := rfl
  have hnw := hS.nw
  have sk : Region.Disjoint ⟨base s kFr, kStack⟩ ⟨s.gpr .x2, 384⟩ := hp.2.2.2.2.2.2.1
  have spk : Region.Disjoint ⟨base s kFr, kStack⟩ ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ := hp.2.2.2.2.2.1
  have hpk : Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x2, 384⟩ := hp.2.2.2.1
  unfold key framed
  refine WP.frameAlloc (by rw [kStack_eq] at hN; omega_using [hN]) (by decide) ?_ ?_
  · rw [hS.push, toNat_addN (by omega_using [hnw, kStack_eq, kFr_eq])]; omega_using []
  unfold keyMain
  refine WP.seq (WP.mono (args_ok hp) fun t ka => ?_)
  refine WP.icalls_of_call (a := t.gpr .x16) rfl ?_
    (Proof.Pbkdf2.Md.AArch64.Any.any_call (n := w.H.hmacInitAnyN) w.ok w.hmacAny w.hmacAnyD (any_args hw hp ka)
      fun s' ha hi ho => ?_)
  · show f.init.find? (fun q => t.syms q.1 == t.gpr .x16) = _
    rw [ka.x16, ka.syms]; exact hp.2.2.2.2.2.2.2.2.2.2.2.2.i
  intro m u hm
  -- The regions the call writes, and the frame's.
  have hsc : Region.Sub ⟨base s kFr + BitVec.ofNat 64 16, 8 * (w.H.W + w.H.S)⟩ ⟨base s kFr, kStack⟩ :=
    Offset.sub_base _ (by omega_using [hA, hw', kStack_eq])
  have hlow : below t.sp 16 = ⟨base s kFr, 16⟩ := by
    show (⟨t.sp - BitVec.ofNat 64 16, 16⟩ : Region) = _
    rw [ka.sp, BitVec.add_sub_cancel]
  have hfr : below s.sp (kFr + 16) = ⟨base s kFr + BitVec.ofNat 64 16, kFr + 16⟩ := by
    show (⟨s.sp - BitVec.ofNat 64 (kFr + 16), kFr + 16⟩ : Region) = _
    rw [Offset.sub_ofNat_eq s.sp (show kFr + 16 ≤ kFr + 32 by omega_using []),
      show kFr + 32 - (kFr + 16) = 16 from by omega_using []]
  have hfrS : Region.Sub ⟨base s kFr + BitVec.ofNat 64 16, kFr + 16⟩ ⟨base s kFr, kStack⟩ :=
    Offset.sub_base _ (by omega_using [kStack_eq, kFr_eq])
  -- The key's 384 bytes, apart from everything the call and the frame wrote.
  have hkey : ∀ (o n : Nat), o + n ≤ 384 → ∀ i < n,
      m (s.gpr .x2 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = s'.mem (s.gpr .x2 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o n hon i hi' => hm.bytes (R := ⟨s.gpr .x2 + BitVec.ofNat 64 o, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hfr]
      exact (sk.symm.sub_left (Offset.sub_base _ hon)).sub_right hfrS)
      (by show n ≤ 2 ^ 64; omega_using [hon]) hi'
  -- The return address, apart from everything the call wrote.
  have hret : s'.mem.read (s.sp - 16) 8 = s.gpr .x30 := by
    have hP : Region.Disjoint ⟨s.sp - 16, 8⟩ ⟨base s kFr + BitVec.ofNat 64 16, 8 * (w.H.W + w.H.S)⟩ := by
      rw [hS.push]; exact Offset.disjoint _ (.inr (by omega_using [hA, hw', kFr_eq]))
        (by omega_using [hnw, kStack_eq, kFr_eq]) (by omega_using [hnw, hA, hw', kStack_eq, kFr_eq])
    rw [ha.frame.read (r := ⟨s.sp - 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hS.push]; exact (sk.sub_left (Offset.sub_base _ (by omega_using [kStack_eq, kFr_eq]))).sub_right
            (Region.sub_prefix (by omega_using [hS192]))
        · rw [hS.push]; exact (sk.sub_left (Offset.sub_base _ (by omega_using [kStack_eq, kFr_eq]))).sub_right
            (Offset.sub_base _ (by omega_using [hS192]))
        · exact hP
        · rw [hlow, hS.push]; exact Offset.disjoint_base _ (by omega_using []) (by omega_using [hnw, kStack_eq, kFr_eq]))
      (by decide), ka.mem]
    exact read_write_self _ _ _
  have hsp' : s'.sp = base s kFr + BitVec.ofNat 64 16 := by rw [ha.sp, ka.sp]
  have hpe : Spec.Sha256.bytesAt (entered kFr s).mem (s.gpr .x0) (s.gpr .x1).toNat =
      Spec.Sha256.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    simp only [Spec.Sha256.bytesAt]
    refine List.map_congr_left fun i hi' => ?_
    have hi' := List.mem_range.mp hi'
    exact (Frame.bytes (R := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩)
      ((Frame.refl _ _).write (List.mem_singleton_self ⟨s.sp - 16, 16⟩) _
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hS.push]
        exact (spk.sub_left (Offset.sub_base _ (by omega_using [kStack_eq, kFr_eq]))).symm)
      (by show (s.gpr .x1).toNat ≤ 2 ^ 64; omega_using [(s.gpr .x1).isLt]) hi')
  rw [ka.mem, hpe] at hi ho
  refine ⟨⟨fun r hr => ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show (popped .x30 (freed kFr s')).gpr r = s.gpr r
    have hfs : s'.sp + BitVec.ofNat 64 kFr = s.sp - 16 := by
      rw [hsp', Offset.add_add, hS.push, Nat.add_comm]
    have hread : (freed kFr s').mem.read (freed kFr s').sp 8 = s.gpr .x30 := by
      simp only [freed]
      exact (congrArg (fun a => s'.mem.read a 8) hfs).trans hret
    show ((freed kFr s').write .x .x30 ((freed kFr s').mem.read (freed kFr s').sp 8)).gpr r = _
    rw [RegUpd.gpr_write]
    by_cases h30 : r = .x30
    · subst h30; simp only [ite_true, hread, BitVec.setWidth_eq]
    · simp only [h30, ite_false]
      exact (ha.cs r hr h30).trans (ka.cs r hr)
  · show (freed kFr s').sp + 16 = s.sp
    show s'.sp + BitVec.ofNat 64 kFr + BitVec.ofNat 64 16 = s.sp
    rw [hsp', Offset.add_add, Offset.add_add, hS.sp, show 16 + (kFr + 16) = kFr + 32 from by omega_using []]
  · refine repr_keep (fun i hi' => ?_) hi
    have := hkey 0 w.H.S (by omega_using [hS192]) i hi'
    rwa [BitVec.add_zero] at this
  · exact repr_keep (fun i hi' => hkey 192 w.H.S (by omega_using [hS192]) i hi') ho

end

/-! ## Constant time -/

/-- The taint analysis accepts `c` from the registers `rs`. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- Code the taint analysis accepts from the registers `rs`, in two runs
whose single-run facts `G₁` and `G₂` agree on them and on `sp`. -/
theorem rel_agree {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa} {rs : List Reg}
    (hag : ∀ s s', P₁ s → P₂ s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r) (hc : Ck rs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => by
      obtain ⟨hsp, hr⟩ := hag s s' h.1 h.2
      exact ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem keyArgs_ck : Ck [.x0, .x1, .x2, .x3] (.block keyArgs) := ⟨_, by taint_decide⟩

section
variable {w : MdHash} {f : Fns} {ns : List String}

/-- `vg_hkdf_key` is constant time: two runs whose public data agree leak the
same trace. -/
theorem key_ct (hw : HOk w) (hns : w.H.hmacInitAnyN ∈ ns) :
    ConstantTime isa (keyR w f ns kStack).pre (keyR w f ns kStack).pub (key f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  obtain ⟨qsp, q0, q1, q2, q3, qn⟩ := hpub
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (key f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold key framed keyMain
  refine RelCT.pushFrame (R := fun _ _ => True) (fun a b ⟨ha, hb⟩ => by rw [ha, hb, qsp]) ?_
  refine RelCT.alloc (R := fun _ _ => True) ?_
  have r1 := rel_agree (P₁ := fun x => x = entered kFr e) (P₂ := fun x => x = entered kFr e')
    (G₁ := KA (w := w) e) (G₂ := KA (w := w) e') (rs := [.x0, .x1, .x2, .x3])
    (fun x y hx hy => by
      subst hx hy
      refine ⟨show e.sp - 16 - BitVec.ofNat 64 kFr = e'.sp - 16 - BitVec.ofNat 64 kFr by rw [qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact q0
      · exact q1
      · exact q2
      · exact q3) keyArgs_ck
    (fun x hx => by subst hx; exact args_ok h) (fun x hx => by subst hx; exact args_ok h')
  refine (r1.seq ?_).mono (fun x y ⟨u, v, ⟨p, q, ⟨hp, hq⟩, hu, hv⟩, hx, hy⟩ =>
    ⟨by rw [hx, hu, hp], by rw [hy, hv, hq]⟩) fun _ _ h => h
  have hb : base e' kFr = base e kFr := by simp only [base, qsp]
  have hcall : RelCT isa (fun t t' => KA (w := w) e t ∧ KA (w := w) e' t') (.call w.H.hmacInitAnyN w.H.hmacInitAny)
      fun _ _ => True :=
    Proof.Pbkdf2.Md.AArch64.Any.any_rel (n := w.H.hmacInitAnyN) w.ok w.hmacAny
      (inn := e.gpr .x2) (out := e.gpr .x2 + BitVec.ofNat 64 192) (k := e.gpr .x0)
      (sc := base e kFr + BitVec.ofNat 64 16) (kl := (e.gpr .x1).toNat)
      fun t t' ⟨ka, ka'⟩ => ⟨any_args hw h ka, by
        have := any_args hw h' ka'; rwa [← q0, ← q1, ← q2, hb] at this,
        by rw [ka.sp, ka'.sp, hb]⟩
  have hi := h.2.2.2.2.2.2.2.2.2.2.2.2.i
  have hi' := h'.2.2.2.2.2.2.2.2.2.2.2.2.i
  cases hf : f.init with
  | nil => rw [hf] at hi; cases hi
  | cons p ts =>
    rw [hf] at hi hi'
    refine RelCT.icalls_of_call hcall fun t t' ⟨ka, ka'⟩ => ⟨e.syms w.H.hmacInitAnyN,
      by simp only [AArch64.icall, ka.x16], by simp only [AArch64.icall, ka'.x16, qn _ hns], ?_, ?_, ?_⟩
    · show (p :: ts).find? (fun q => t.syms q.1 == e.syms w.H.hmacInitAnyN) = _
      rw [ka.syms]; exact hi
    · show (p :: ts).find? (fun q => t'.syms q.1 == e.syms w.H.hmacInitAnyN) = _
      rw [ka'.syms, qn _ hns]; exact hi'
    · simp only [AArch64.addrs]

end

end VG.Proof.Hkdf.AArch64
