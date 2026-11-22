module

public import VerifiedGarbage.Proof.HmacTable.X86_64
public import VerifiedGarbage.Impl.Hkdf.X86_64
public import VerifiedGarbage.Spec.Hkdf.Table
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Hkdf.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# HKDF on x86-64: `vg_hkdf_key`, correct

The contract the proof is written against (`keyR`), for the table `hmac` of
one variant `w` (`MdHash`), whose functions an indirect call of `f`'s
reaches: `key(prk, prk_len, key, hmac)` makes the 384 bytes at `key` hold
HMAC's states keyed with `PRK` (`Spec.Hkdf.Keyed`, with `w`'s streaming
states). In its frame (`kFr` bytes, the working space), `keyArgs` moves
`init`'s arguments into place and its address into `r11` (`args_ok`); HMAC's
`init` for a key of any length, through the table, writes the states
(`init_ok`), which the frame's release leaves as they are (`key_correct`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86_64

open VG.X86_64 VG.X86_64.Steps
open VG.Impl.Hkdf.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (TabOK TabMem)
open Spec.Sha256 (bytesAt)

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

/-- The stack `vg_hkdf_key` uses: its frame, and below it the 32 bytes the
call of `init` takes to be apart from its buffers. -/
def kStack : Nat := kFr + 32

/-- `key(prk, prk_len, key, hmac)`, with `N` bytes of stack, for the table
`hmac` of `w`, whose functions an indirect call of `f`'s reaches, with the
addresses of the functions `ns` public. -/
def keyR (w : MdHash) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let prk : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let key : Region := ⟨s.gpr .rdx, 384⟩
    let tab : Region := ⟨s.gpr .rcx, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .rsp).toNat ∧ s.rd = [prk, tab] ∧ s.wr = [key] ∧ prk.Disjoint key ∧ key.Disjoint tab ∧
      ret.Disjoint prk ∧ ret.Disjoint key ∧ ret.Disjoint tab ∧
      stk.Disjoint prk ∧ stk.Disjoint key ∧ stk.Disjoint tab ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 384 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 48 ≤ 2 ^ 64 ∧ TabMem w.H s.syms (s.gpr .rcx) s.mem ∧ TabOK w.H f s.syms
  post s s' := Spec.Hkdf.Keyed w.ok.SH s'.mem (s.gpr .rdx) (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-! ## Addresses -/

theorem ea_at (t : State) (b : Reg) (d : Nat) : t.ea (Impl.Mgf1.X86_64.at_ b d) = t.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, Impl.Mgf1.X86_64.at_, BitVec.ofInt_natCast]

theorem ea_sp (t : State) (d : Nat) : t.ea (Impl.Mgf1.X86_64.sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, Impl.Mgf1.X86_64.sp, BitVec.ofInt_natCast]

/-! ## `vg_hkdf_key` -/

/-- The state the frame's body starts in. -/
structure KPre (w : MdHash) (f : Fns) (s a : State) : Prop where
  hw : HOk w
  rsp : a.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 kFr
  gpr : ∀ r, r ≠ .rsp → a.gpr r = s.gpr r
  mem : a.mem = s.mem
  rd : a.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rcx, 48⟩]
  wr : a.wr = [⟨s.gpr .rsp - BitVec.ofNat 64 kFr, kFr⟩, ⟨s.gpr .rdx, 384⟩]
  syms : a.syms = s.syms
  p_k : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rdx, 384⟩
  s_p : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 kStack, kStack⟩ ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  s_k : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 kStack, kStack⟩ ⟨s.gpr .rdx, 384⟩
  r_k : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 384⟩
  sp : kStack ≤ (s.gpr .rsp).toNat
  nk : (s.gpr .rdx).toNat + 384 ≤ 2 ^ 64
  np : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  tm : TabMem w.H s.syms (s.gpr .rcx) s.mem
  tok : TabOK w.H f s.syms
  nt : (s.gpr .rcx).toNat + 48 ≤ 2 ^ 64

theorem kFr_eq : kFr = 3104 := rfl
theorem kStack_eq : kStack = 3136 := rfl

theorem sx192 : (BitVec.ofNat 32 192).signExtend 64 = BitVec.ofNat 64 192 := by decide

section
variable {w : MdHash} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem kpre {s : State} (hw : HOk w) (hp : (keyR w f ns kStack).pre s) : KPre w f s (allocState kFr s) := by
  obtain ⟨hsp, hrd, hwr, pk, kt, rp, rk, rt, sp', sk, st, np, nk, nt, tm, tok⟩ := hp
  exact ⟨hw, allocState_rsp' _ _, fun r hr => allocState_gpr' _ _ hr, rfl, hrd,
    by show (_ : Region) :: s.wr = _; rw [hwr], rfl, pk, sp', sk, rk, hsp, nk, np, tm, tok, nt⟩

/-- The frame, and below it the 32 bytes the call of `init` takes to be apart
from its buffers, within the stack the contract gives. -/
theorem fr_sub (s : State) {n : Nat} (hn : n ≤ kFr) :
    Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 kFr, n⟩ ⟨s.gpr .rsp - BitVec.ofNat 64 kStack, kStack⟩ :=
  Offset.sub_below _ (by rw [kStack_eq, kFr_eq]; omega_using []) (by rw [kStack_eq, kFr_eq] at *; omega_using [hn])

theorem low_sub (s : State) :
    Region.Sub (below (s.gpr .rsp - BitVec.ofNat 64 kFr) 32) ⟨s.gpr .rsp - BitVec.ofNat 64 kStack, kStack⟩ := by
  show Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 kFr - BitVec.ofNat 64 32, 32⟩ _
  rw [Offset.sub_sub_ofNat]
  exact Region.sub_prefix (by rw [kStack_eq]; omega_using [])

/-- What `keyArgs` leaves: `init`'s arguments, and its address in `r11`. -/
structure KA (s t : State) : Prop where
  rdi : t.gpr .rdi = s.gpr .rdx
  rsi : t.gpr .rsi = s.gpr .rdx + BitVec.ofNat 64 192
  rdx : t.gpr .rdx = s.gpr .rdi
  rcx : t.gpr .rcx = s.gpr .rsi
  r8 : t.gpr .r8 = s.gpr .rsp - BitVec.ofNat 64 kFr
  r11 : t.gpr .r11 = s.syms w.H.hmacInitAnyN
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  rsp : t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 kFr
  mem : t.mem = s.mem
  rd : t.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rcx, 48⟩]
  wr : t.wr = [⟨s.gpr .rsp - BitVec.ofNat 64 kFr, kFr⟩, ⟨s.gpr .rdx, 384⟩]
  syms : t.syms = s.syms

theorem args_ok {s a : State} (k : KPre w f s a) : WP isa (.block keyArgs) a (KA (w := w) s) := by
  unfold keyArgs
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_addi fun t₄ u₄ =>
    wp_mov fun t₅ u₅ => wp_mov fun t₆ u₆ => wp_mov fun t₇ u₇ => wp_mov fun t₈ u₈ => ?_
  have h11 : t₈.gpr .r11 = s.gpr .rcx := by
    upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]; exact k.gpr _ (by decide)
  have hm₈ : t₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, k.mem]
  have hrd₈ : t₈.rd = a.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr₈ : t₈.wr = a.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_movm (a := s.gpr .rcx + BitVec.ofNat 64 0) (by rw [ea_at, h11])
    ⟨⟨s.gpr .rcx, 48⟩, List.mem_append_left _ (by rw [hrd₈, k.rd]; simp),
      Offset.contains_base _ (by decide) (by decide)⟩ fun t₉ u₉ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r11 → r ≠ .r8 → r ≠ .rdi → r ≠ .rdx → r ≠ .rax → r ≠ .rsi → r ≠ .rcx →
      t₉.gpr r = a.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    rw [u₉.other r h1, u₈.other r h2, u₇.other r h3, u₆.other r h4, u₅.other r h5, u₄.other r h6,
      u₃.other r h6, u₂.other r h7, u₁.other r h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr hr' => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other]
    exact k.gpr _ (by decide)
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₂.other, u₁.other]
    rw [k.gpr _ (by decide), sx192]
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
    exact k.gpr _ (by decide)
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]
    exact k.gpr _ (by decide)
  · upd_simp [u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
    exact k.rsp
  · rw [u₉.gpr, hm₈, show s.gpr .rcx + BitVec.ofNat 64 0 = s.gpr .rcx + BitVec.ofNat 64 0 from rfl]
    exact k.tm.1
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
    exact k.gpr r hr'
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact k.rsp
  · rw [u₉.mem, hm₈]
  · rw [u₉.rd, hrd₈, k.rd]
  · rw [u₉.wr, hwr₈, k.wr]
  · rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms, k.syms]

/-- `init`'s regions, from what `keyArgs` leaves. -/
theorem any_args {s a t : State} (k : KPre w f s a) (ka : KA (w := w) s t) :
    Proof.Pbkdf2.Md.X86_64.Any.AnyArgs (H := w.H) t (s.gpr .rdx) (s.gpr .rdx + BitVec.ofNat 64 192) (s.gpr .rdi)
      (s.gpr .rsp - BitVec.ofNat 64 kFr) (s.gpr .rsi).toNat := by
  have hS := k.hw.hS; have hA := k.hw.hA
  have hw' : work = 3104 := rfl
  have hsc : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 kFr, 8 * (w.H.W + w.H.S)⟩
      ⟨s.gpr .rsp - BitVec.ofNat 64 kStack, kStack⟩ := fr_sub s (by rw [kFr_eq]; omega_using [hA, hw'])
  have hlow := low_sub s
  have hkS : Region.Sub ⟨s.gpr .rdx, w.H.S⟩ ⟨s.gpr .rdx, 384⟩ := Region.sub_prefix (by omega_using [hS])
  have hoS : Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 192, w.H.S⟩ ⟨s.gpr .rdx, 384⟩ :=
    Offset.sub_base _ (by omega_using [hS])
  have hspF : (s.gpr .rsp - BitVec.ofNat 64 kFr).toNat = (s.gpr .rsp).toNat - kFr := by
    have := k.sp
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; rw [kStack_eq] at this; rw [kFr_eq]; omega_using [this]),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [kFr_eq]; omega_using [])]
  have hbelow : below (t.gpr .rsp) 32 = below (s.gpr .rsp - BitVec.ofNat 64 kFr) 32 := by rw [ka.rsp]
  refine ⟨ka.rdi, ka.rsi, ka.rdx, ?_, ka.r8, ?_, ?_, ?_, (k.s_k.symm.sub_left hkS).sub_right hsc,
    (k.s_k.symm.sub_left hoS).sub_right hsc, k.p_k.sub_right hkS, k.p_k.sub_right hoS, (k.s_p.symm).sub_right hsc,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [ka.rcx]
  · exact VG.Covers.left (by rw [ka.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
  · rw [ka.wr]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨s.gpr .rdx, 384⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; omega_using [hS]⟩
    · exact ⟨⟨s.gpr .rdx, 384⟩, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩
    · exact ⟨⟨s.gpr .rsp - BitVec.ofNat 64 kFr, kFr⟩, by simp, 0, (BitVec.add_zero _).symm,
        by dsimp only; rw [kFr_eq]; omega_using [hA, hw']⟩
  · have := Offset.base_disjoint (s.gpr .rdx) (e := 192) (n := w.H.S) (k := w.H.S) (by omega_using [hS])
      (by omega_using [hS])
    exact this
  · rw [hbelow]; exact (k.s_k.sub_left hlow).sub_right hkS
  · rw [hbelow]; exact (k.s_k.sub_left hlow).sub_right hoS
  · rw [hbelow]; exact k.s_p.sub_left hlow
  · rw [hbelow]
    show Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 kFr - BitVec.ofNat 64 32, 32⟩ _
    have := Offset.base_disjoint (s.gpr .rsp - BitVec.ofNat 64 kFr - BitVec.ofNat 64 32) (e := 32)
      (n := 8 * (w.H.W + w.H.S)) (k := 32) (Nat.le_refl _) (by omega_using [hA, hw'])
    rwa [BitVec.sub_add_cancel] at this
  · rw [hspF]; have := (s.gpr .rsp).isLt; rw [kFr_eq] at *; omega_using [hA, hw', this]

/-- A state at `p` represents the same message in memory that agrees with it
there. -/
theorem repr_keep {m m' : Mem} {p : Addr} {msg : List Byte}
    (h : ∀ i < w.H.S, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) (hr : w.ok.SH.Repr m p msg) :
    w.ok.SH.Repr m' p msg :=
  w.ok.stream.repr _ _ _ _ _ h hr

/-- `vg_hkdf_key`: its frame, the arguments, and HMAC's `init` through the table. -/
theorem key_correct {s : State} (hw : HOk w) (hp : (keyR w f ns kStack).pre s) :
    WP isa (key f) s fun s' => gprPreserved s s' ∧ (keyR w f ns kStack).post s s' := by
  have k := kpre hw hp
  have hsp := k.sp
  have hS := hw.hS
  have hwr0 : s.wr = [⟨s.gpr .rdx, 384⟩] := hp.2.2.1
  unfold key
  refine alloc_frame_ok (by decide) (by rw [kStack_eq] at hsp; rw [kFr_eq]; omega_using [hsp]) ?_
  unfold keyMain
  refine WP.seq (WP.mono (args_ok k) fun t ka => ?_)
  refine WP.icalls_of_call (a := t.gpr .r11) rfl ?_
    (Proof.Pbkdf2.Md.X86_64.Any.any_call (n := w.H.hmacInitAnyN) w.ok w.hmacAny w.hmacAnyNs w.hmacAnyD (any_args k ka)
      (s.gpr .rsi).isLt ?_)
  · show f.init.find? (fun q => t.syms q.1 == t.gpr .r11) = _
    rw [ka.r11, ka.syms]; exact k.tok.i
  intro s' hrd hwr hcs hfr hi ho
  have hrsp' : s'.gpr .rsp = (allocState kFr s).gpr .rsp := by rw [hcs .rsp (by decide), ka.rsp, allocState_rsp']
  refine ⟨hrsp', by rw [hwr, ka.wr]; show _ = (_ : Region) :: s.wr; rw [hwr0], fun m u hm => ?_⟩
  have hkr : ∀ (o n : Nat), o + n ≤ 384 → ∀ i < n,
      m (s.gpr .rdx + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = s'.mem (s.gpr .rdx + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o n hon i hi' => hm.bytes (R := ⟨s.gpr .rdx + BitVec.ofNat 64 o, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (k.s_k.symm.sub_left (Offset.sub_base _ hon)).sub_right (fr_sub s (Nat.le_refl _)))
      (by show n ≤ 2 ^ 64; omega_using [hon]) hi'
  -- The return address, apart from everything the call and the frame wrote.
  have hret : m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    have h₁ : m.readW (s.gpr .rsp) 64 = s'.mem.readW (s.gpr .rsp) 64 :=
      hm.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint_below _ (by rw [kFr_eq]; omega_using [])) (by decide)
    have h₂ : s'.mem.readW (s.gpr .rsp) 64 = t.mem.readW (s.gpr .rsp) 64 := by
      refine hfr.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact k.r_k.sub_right (Region.sub_prefix (by omega_using [hS]))
      · exact k.r_k.sub_right (Offset.sub_base _ (by omega_using [hS]))
      · exact (Offset.base_disjoint_below _ (by rw [kFr_eq]; omega_using [])).sub_right
          (Region.sub_prefix (by have hA := hw.hA; have hw' : work = 3104 := rfl; rw [kFr_eq]; omega_using [hA, hw']))
      · rw [ka.rsp]
        show Region.Disjoint _ ⟨s.gpr .rsp - BitVec.ofNat 64 kFr - BitVec.ofNat 64 24, 24⟩
        rw [Offset.sub_sub_ofNat]
        exact (Offset.base_disjoint_below _ (by rw [kFr_eq]; omega_using [])).sub_right (Region.sub_prefix (by omega_using []))
    rw [h₁, h₂, ka.mem]
  refine ⟨⟨fun r hr => ?_, hret⟩, ⟨?_, ?_⟩⟩
  · by_cases hr' : r = .rsp
    · subst hr'; exact freeState_rsp hrsp'
    · show (s'.setReg .rsp (s'.gpr .rsp + BitVec.ofNat 64 kFr)).gpr r = _
      rw [RegUpd.gpr_setReg_of_ne _ _ hr', hcs r hr, ka.cs r hr hr']
  · rw [ka.mem] at hi
    refine repr_keep (fun i hi' => ?_) hi
    have := hkr 0 w.H.S (by omega_using [hS]) i hi'
    rwa [BitVec.add_zero] at this
  · rw [ka.mem] at ho
    exact repr_keep (fun i hi' => hkr 192 w.H.S (by omega_using [hS]) i hi') ho

end

/-! ## Constant time -/

/-- The taint analysis accepts `c` from the registers `rs`. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- Code the taint analysis accepts from the registers `rs`, in two runs
whose single-run facts `G₁` and `G₂` agree on them. -/
theorem rel_agree {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa} {rs : List Reg}
    (hag : ∀ s s', P₁ s → P₂ s' → ∀ r ∈ rs, s.gpr r = s'.gpr r) (hc : Ck rs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2)) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem keyArgs_ck : Ck [.rdi, .rsi, .rdx, .rcx, .rsp] (.block keyArgs) := ⟨_, by taint_decide⟩

section
variable {w : MdHash} {f : Fns} {ns : List String}

/-- `vg_hkdf_key` is constant time: two runs whose public data agree leak the
same trace. -/
theorem key_ct (hw : HOk w) (hns : w.H.hmacInitAnyN ∈ ns) :
    ConstantTime isa (keyR w f ns kStack).pre (keyR w f ns kStack).pub (key f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  obtain ⟨qsp, q0, q1, q2, q3, qn⟩ := hpub
  have k := kpre hw h; have k' := kpre hw h'
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (key f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold key keyMain
  refine RelCT.alloc (R := fun _ _ => True) ?_
  have r1 := rel_agree (P₁ := fun x => x = allocState kFr e) (P₂ := fun x => x = allocState kFr e')
    (G₁ := KA (w := w) e) (G₂ := KA (w := w) e') (rs := [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun x y hx hy r hr => by
      subst hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q0]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q1]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q2]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q3]
      · rw [allocState_rsp', allocState_rsp', qsp]) keyArgs_ck
    (fun x hx => by subst hx; exact args_ok k) (fun x hx => by subst hx; exact args_ok k')
  refine (r1.seq ?_).mono (fun x y ⟨u, v, ⟨hu, hv⟩, hx, hy⟩ => ⟨by rw [hx, hu], by rw [hy, hv]⟩) fun _ _ h => h
  have hcall : RelCT isa (fun t t' => KA (w := w) e t ∧ KA (w := w) e' t') (.call w.H.hmacInitAnyN w.H.hmacInitAny)
      fun _ _ => True :=
    Proof.Pbkdf2.Md.X86_64.Any.any_rel (n := w.H.hmacInitAnyN) w.ok w.hmacAny
      (inn := e.gpr .rdx) (out := e.gpr .rdx + BitVec.ofNat 64 192) (k := e.gpr .rdi)
      (sc := e.gpr .rsp - BitVec.ofNat 64 kFr) (kl := (e.gpr .rsi).toNat)
      fun t t' ⟨ka, ka'⟩ => ⟨any_args k ka, by
        have := any_args k' ka'; rwa [← q0, ← q1, ← q2, ← qsp] at this,
        by rw [ka.rsp, ka'.rsp, qsp]⟩
  have hi := k.tok.i
  have hi' := k'.tok.i
  cases hf : f.init with
  | nil => rw [hf] at hi; cases hi
  | cons p ts =>
    rw [hf] at hi hi'
    refine RelCT.icalls_of_call hcall fun t t' ⟨ka, ka'⟩ => ⟨e.syms w.H.hmacInitAnyN,
      by simp only [X86_64.icall, ka.r11], by simp only [X86_64.icall, ka'.r11, qn _ hns], ?_, ?_, ?_⟩
    · show (p :: ts).find? (fun q => t.syms q.1 == e.syms w.H.hmacInitAnyN) = _
      rw [ka.syms]; exact hi
    · show (p :: ts).find? (fun q => t'.syms q.1 == e.syms w.H.hmacInitAnyN) = _
      rw [ka'.syms, qn _ hns]; exact hi'
    · simp only [X86_64.addrs]

end

end VG.Proof.Hkdf.X86_64
