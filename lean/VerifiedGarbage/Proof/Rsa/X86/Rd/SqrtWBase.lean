module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Eq
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The square root by words on i686: what its pieces share

The header words the square root keeps (`lsN`), the state before each digit
step (`SqI`: the root `s` so far doubled in `sqD`, the remainder in place of
the radicand's top words in `wR`, `d` and its reciprocal in the header), the
call's argument `n_len` (`KS.mlen`), and the or of a wide array's words
(`KS.orAll`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (wq MLen)

/-- The header words the square root reads: `sqrt`'s own (`sqSlotsW`, kept). -/
abbrev sqSlotsW : List Nat := [sOkDE, sLt, sExact, sOk4]

/-- The header words kept from `normX` on: `X = 0`, the word and bit shifts, and `sqSlotsW`. -/
abbrev lsN : List Nat := [sZf, sKw, sZb, sOkDE, sLt, sExact, sOk4]

/-- The digits so far, with `j` digits (`β = 2^32`) left, of the normalized radicand `X` of
`2 W'` words, `W' = wq a`: the root `s` of `⌊X / β^(2 j)⌋` (`W' - j` words, its top word
`d ≥ 2^31` in the header with its reciprocal) doubled at word `j` of `sqD`, and its remainder `r`
in place of `X`'s top words in `wR`. -/
def SqR (a X j s r : Nat) (AW V : Nat → Nat) : Prop :=
  AW sqD = 2 * s * 2 ^ (32 * j) ∧ AW wR = r * 2 ^ (64 * j) + X % 2 ^ (64 * j) ∧
    s * s + r = X / 2 ^ (64 * j) ∧ r ≤ 2 * s ∧
    V VG.Impl.Rsa.X86.WordModRt.oD = s / 2 ^ (32 * (wq a - 1 - j)) ∧
    2 ^ 31 ≤ V VG.Impl.Rsa.X86.WordModRt.oD ∧ s < 2 ^ (32 * (wq a - j)) ∧
    V VG.Impl.Rsa.X86.WordModRt.oV = (2 ^ 64 - 1) / V VG.Impl.Rsa.X86.WordModRt.oD - 2 ^ 32

/-- The state before the digit step with `j` in `sCt` (and after the last, `j = 0`): `SqR`, the
header words `lsN` as in `V0`. -/
def SqI (g : Geo) (s0 : State) (A V0 : Nat → Nat) (a X j : Nat) (u : State) : Prop :=
  ∃ AW V s r, KS g s0 A [aD, aZero] AW [wR, sqD] V
      (sCt :: VG.Impl.Rsa.X86.WordModRt.oD :: VG.Impl.Rsa.X86.WordModRt.oV :: lsN) u ∧
    (∀ d ∈ lsN, V d = V0 d) ∧ V sCt = j ∧ SqR a X j s r AW V

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

end

open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86.Rt (PtrAt)

/-- The loop or'ing `N` words at `esi` into `ecx`, `edx` counting their bytes. -/
abbrev orEsiLoop : Prog isa :=
  .loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne

theorem orEsiLoop_ok {s : State} {B : Addr} {Z x N : Nat} (hw : VG.Proof.Mont.X86.Rt.Ws s B Z) (hN : 0 < N)
    (hx : x + 4 * N ≤ Z) (hp : PtrAt s B .esi x) (hn : (s.gpr .edx).toNat = 4 * N) :
    WP isa orEsiLoop s fun u => u.mem = s.mem ∧
      (u.gpr .ecx = 0 ↔ s.gpr .ecx = 0 ∧ val32 s.mem B x N = 0) ∧ Keeps [.ecx, .edx, .esi] s u := by
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop hN (fun j t => Keeps [.ecx, .edx, .esi] s t ∧
      t.mem = s.mem ∧ PtrAt t B .esi (x + 4 * j) ∧ (t.gpr .edx).toNat = 4 * (N - j) ∧
      (t.gpr .ecx = 0 ↔ s.gpr .ecx = 0 ∧ ∀ i < j, s.mem.readW (off B (x + 4 * i)) 32 = 0)) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using hp, by simpa using hn, by simp⟩)
    fun u ⟨K, m, _, _, e⟩ =>
      ⟨m, e.trans (and_congr_right fun _ => (VG.Proof.Rsa.X86.WordRt.val32_zero_iff _ _ _ _).symm), K⟩
  rintro j t hj ⟨K, m, p, n, e⟩
  have ht := hw.of_keeps K
  refine wp_orS (VG.Proof.Mont.X86.Rt.readSrc_ptr ht p (d := 0) (by omega)) fun s1 U1 =>
    wp_addS rfl fun s2 U2 _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun s3 U3 z3 => WP.block_nil ?_
  have K3 : Keeps [.ecx, .edx, .esi] t s3 :=
    ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))
  have m3 : s3.mem = t.mem := by rw [U3.mem, U2.mem, U1.mem]
  obtain ⟨cn, cz⟩ := VG.Proof.Mont.X86.Rt.count_zf n hj
  refine ⟨⟨K.trans K3, m3.trans m, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, U3.other _ (by decide), U2.gpr, U1.other _ (by decide)]; exact VG.Proof.Bignum.X86.PublicRt.ptr4 p
  · rw [U3.gpr, U2.other _ (by decide), U1.other _ (by decide)]; exact cn
  · rw [U3.other _ (by decide), U2.other _ (by decide), U1.gpr, m, Nat.add_zero]
    change (_ ||| _) = 0#32 ↔ _
    rw [BitVec.or_eq_zero_iff]
    change t.gpr .ecx = 0 ∧ _ ↔ _
    rw [e]
    constructor
    · rintro ⟨⟨c0, old⟩, last⟩; refine ⟨c0, fun i hi => ?_⟩
      by_cases eq : i = j
      · subst eq; exact last
      · exact old i (by omega)
    · rintro ⟨c0, all⟩; exact ⟨⟨c0, fun i hi => all i (by omega)⟩, all j (by omega)⟩
  · rw [z3, U2.other _ (by decide), U1.other _ (by decide), cz]

open VG.Impl.Rsa.X86.KeyRt (arrPtr bytesB)
open VG.Proof.Rsa.X86.KeyRt (kw arrPtr_ok lenSrc bytesB_ok)

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `ecx` zero exactly where the wide `[j]` is zero: its `W` words or'ed. -/
theorem KS.orAll {j : Nat} (h : KS g s0 A live AW liveW V ls s) (hj : j ∈ liveW) :
    WP isa (.seq (.block (arrPtr wid .esi j .edx ++ bytesB wid .edx ++ ([.mov .ecx (.imm 0)] : List Instr))) orEsiLoop) s
      fun t => KS g s0 A live AW liveW V ls t ∧ Keeps opRegs s t ∧ (t.gpr .ecx = 0 ↔ AW j = 0) := by
  have hr := h.rtW
  have jl := h.liveW_lt j hj
  have fit := hr.ws.arr_fit jl
  have nw := hr.ws.workspace.nowrap
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound hr.lenLe
  simp only [S] at fit
  refine WP.seq ?_
  rw [List.append_assoc]
  refine arrPtr_ok (lenSrc hr) hr.lenLe hr.edi (r := .esi) (t := .edx) (j := j) (by decide) (by decide)
    (by omega) fun u₁ U₁ m₁ p₁ _ => ?_
  have h₁ := hr.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine bytesB_ok (lenSrc h₁) h₁.lenLe fun u₂ U₂ m₂ e₂ => ?_
  refine wp_movS (v := 0) rfl fun u₃ U₃ _ => WP.block_nil ?_
  have K₃ : Keeps [.esi, .edx, .ecx] s u₃ :=
    (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans (U₃.keeps.mono (by decide)))
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, m₂, m₁]
  have p₃ : PtrAt u₃ g.B .esi (arr (kw (16 * g.n + 24)) j) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.1 _ (by decide)]; exact p₁
  have n₃ : (u₃.gpr .edx).toNat = 4 * kw (16 * g.n + 24) := by rw [U₃.other _ (by decide)]; exact e₂
  have c₃ : u₃.gpr .ecx = 0 := by rw [U₃.gpr]
  refine WP.mono (orEsiLoop_ok (hr.rt.of_keeps K₃) (by rw [kw_wid]; change 0 < 2 * (2 * g.n + 2) + 2; omega)
    (by have := fit; omega) p₃ n₃) fun t ⟨mt, et, Kt⟩ => ?_
  have K : Keeps opRegs s t := (K₃.mono (by decide)).trans (Kt.mono (by decide))
  refine ⟨h.of_rest K (fun x hx => hx) (by rw [mt, m₃]), K, ?_⟩
  rw [et, m₃, kw_wid]
  change (u₃.gpr .ecx = 0 ∧ num s.mem g.B g.W j = 0) ↔ _
  rw [h.arrsW j hj]
  exact ⟨fun e => e.2, fun e => ⟨c₃, e⟩⟩

end

end VG.Proof.Rsa.X86.Recover
