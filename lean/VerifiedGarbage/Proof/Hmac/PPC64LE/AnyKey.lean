module

public import VerifiedGarbage.Proof.Hmac.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.EntryBranch
import all Init.Data.Nat.Bitwise.Basic

/-!
# HMAC-SHA-256 on PPC64LE: `init` for a key of any length, choosing on entry

`initAny` sets `r12` to a nonzero value exactly when `key_len` (`r6`) is more
than 64 (`entryCmp`, `entry_run`) and runs `long` (`Shared.long`, for a key
longer than a block) or `short` (`Shared.init`, `initContract`), both with
912 bytes of stack (`Verified.entryBranch`). The comparison writes only `r11`
and `r12`, which no contract reads, and leaks nothing; the branch depends
only on `key_len`, which is public. The same structure as AArch64's
(`VG.Proof.Pbkdf2.Md.AArch64.initEntry_verified`).
-/

@[expose] public section

namespace VG.Proof.Hmac.PPC64LE.AnyKey

open VG.PPC64LE

/-- What `entryCmp` leaves of a state: all but `r11` and `r12`. -/
structure Ran (s u : State) : Prop where
  g : ∀ r, r ≠ .r11 → r ≠ .r12 → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  lr : u.lr = s.lr
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

/-- `(x >>> 7) + ((x &&& 127) + 63) >>> 7` is nonzero exactly when `x` is
more than 64. -/
theorem cmp_ne (x : BitVec 64) :
    ((x >>> 7) + ((x &&& BitVec.ofNat 64 127) + BitVec.ofNat 64 63) >>> 7 != 0) =
      decide (64 < x.toNat) := by
  have hx := x.isLt
  have ha : (x &&& BitVec.ofNat 64 127).toNat = x.toNat % 128 := by
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 127).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hb : ((x &&& BitVec.ofNat 64 127) + BitVec.ofNat 64 63).toNat = x.toNat % 128 + 63 := by
    rw [BitVec.toNat_add, ha, show (BitVec.ofNat 64 63).toNat = 63 from rfl]
    omega
  have hv : ((x >>> 7) + ((x &&& BitVec.ofNat 64 127) + BitVec.ofNat 64 63) >>> 7).toNat =
      x.toNat / 128 + (x.toNat % 128 + 63) / 128 := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, hb, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    omega
  by_cases h : 64 < x.toNat
  · rw [decide_eq_true h]
    simp only [bne_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [hv] at this
    simp at this
    omega
  · rw [decide_eq_false h]
    simp only [bne_eq_false_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hv]
    simp
    omega

theorem entry_run (s : State) :
    ∃ u, execBlock isa Impl.Hmac.PPC64LE.entryCmp s = some (u, []) ∧ Ran s u ∧
      eval (.nonzero .d .r12) u = some (decide (64 < (s.gpr .r6).toNat)) := by
  refine ⟨_, rfl, ⟨fun r h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [State.write, h11, h12]
  · simp only [eval, State.read, State.write, Size.ext, reduceCtorEq, ↓reduceIte, Option.some.injEq]
    exact cmp_ne _

/-- `init` for a key of any length, against the shared contract. -/
theorem initAny : Verified PPC64LE.target Impl.Hmac.PPC64LE.initAny
    (Spec.Hmac.sha256I.initAnyKeyContract PPC64LE.abi (48 + 864)) := by
  have hp : ∀ r ∈ preserved, r ≠ .r11 ∧ r ≠ .r12 := by decide
  have hsat : ∃ s, (Spec.Hmac.sha256I.initAnyKeyContract PPC64LE.abi (48 + 864)).pre s := by
    implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs]
      [Shared.longFrameSat] using Shared.longFrameSat
  refine Verified.entryBranch (p := fun s => decide (64 < (s.gpr .r6).toNat))
    (fun _ => []) Shared.long Shared.init (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, r, ev⟩ := entry_run s
    have g3 := r.g .r3 (by decide) (by decide)
    have g4 := r.g .r4 (by decide) (by decide)
    have g5 := r.g .r5 (by decide) (by decide)
    have g6 := r.g .r6 (by decide) (by decide)
    have abi : ∀ s', PPC64LE.target.abiPreserved u s' → PPC64LE.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by
        obtain ⟨h11, h12⟩ := hp x hx
        rw [a.1 x hx, r.g x h11 h12], by rw [a.2.1, r.sp], by rw [a.2.2, r.lr]⟩
    refine ⟨u, e, ev, fun hl => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hl => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · have hk : 64 < (s.gpr .r6).toNat := of_decide_eq_true hl
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs] at hs
      sig_pre [Shared.longContract, Shared.longPre, Impl.Hmac.PPC64LE.longFrame, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs]
      rw [g3, g4, g5, g6, r.sp, r.rd, r.wr]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hs
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_post [Shared.longContract, Shared.longPre, Impl.Hmac.PPC64LE.longFrame, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
    · have hk : (s.gpr .r6).toNat ≤ 64 := by have := of_decide_eq_false hl; omega
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs] at hs
      sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs]
      rw [g3, g4, g5, g6, r.sp, r.rd, r.wr]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hs
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, r, -⟩ := entry_run s
    obtain ⟨u₀', e₀', r', -⟩ := entry_run s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
      PPC64LE.argRegs] at hq'
    obtain ⟨qsp, q3, q4, q5, q6⟩ := hq'
    have e3 := r.g .r3 (by decide) (by decide)
    have e4 := r.g .r4 (by decide) (by decide)
    have e5 := r.g .r5 (by decide) (by decide)
    have e6 := r.g .r6 (by decide) (by decide)
    have e3' := r'.g .r3 (by decide) (by decide)
    have e4' := r'.g .r4 (by decide) (by decide)
    have e5' := r'.g .r5 (by decide) (by decide)
    have e6' := r'.g .r6 (by decide) (by decide)
    refine ⟨rfl, by rw [q6], fun _ => ?_, fun _ => ?_⟩
    · sig_pub [Shared.longContract, Shared.longPre, Impl.Hmac.PPC64LE.longFrame, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
        PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6']
      exact ⟨qsp, q3, q4, q5, q6⟩
    · sig_pub [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
        PPC64LE.abi, PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6']
      exact ⟨qsp, q3, q4, q5, q6⟩

end VG.Proof.Hmac.PPC64LE.AnyKey
