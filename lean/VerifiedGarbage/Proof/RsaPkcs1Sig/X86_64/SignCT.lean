module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignEntry
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignEntry
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_sign` on x86-64: constant time

As for `vg_rsa_pkcs1_recover` (`RecoverCT.lean`): each point of the code is
described, in each run, by what correctness says of it from that run's entry
state, which agrees with an anchor on the public data (`At`). The blocks are
checked by the taint analysis from the registers this fixes, the branch on
`encode`'s result is fixed by it too (whether the encoding succeeds depends
on the hash function, the length of the hash value and `k` alone), and the
call is constant time for `vg_rsa_private_checked`'s contract, whose public
data (its registers and stack arguments, `n` and `e`) it fixes. The zeros to
`out` and to `EM` take their address and length from the frame's slots:
their loads are pieces of their own, and the loops after them are checked
from the registers correctness fixes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Impl.RsaPkcs1Sig.X86_64.Recover (zeroOut)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract)
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (test0_ok entry_regs regs_eq)

/-! ## The taint checks -/

theorem wipeLoop_taint {Φ : State → State → Prop} (h : Pins Φ [.r10, .r11]) :
    RelCT isa (Two Φ)
      (.loop (.block [.store8 { base := .r10 } .rdx, .alu .add .r10 (.imm 1), .alu .sub .r11 (.imm 1)]) .ne)
      fun _ _ => True := two_taint [.r10, .r11] h (by taint_decide)

/-! ## Entry states and the anchor -/

/-- An entry state `s` of a run, which agrees with `a` on the public data,
and is related to it by `X` (`vg_rsa_pkcs1_sign_precomputed`'s further
public data, `SignPCT.lean`). -/
def Sib (X : State → State → Prop) (a s : State) : Prop := (PreS s ∧ sigContract.pub a s) ∧ X a s

theorem pub_refl (s : State) : sigContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

variable {X : State → State → Prop}

theorem Sib.gpr {a s : State} (h : Sib X a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.1.2.1 r hr).symm

theorem Sib.h {a s : State} (h : Sib X a s) : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32 :=
  h.1.2.2.1.symm

theorem Sib.arg {a s : State} (h : Sib X a s) {i : Nat} (hi : 1 ≤ i) (hi' : i < 15) : stackArg s i = stackArg a i := by
  have := (List.map_inj_left.mp h.1.2.2.2.1) (i - 1) (List.mem_range.mpr (by omega_using [hi']))
  simp only [show i - 1 + 1 = i by omega_using [hi]] at this
  exact this.symm

theorem Sib.n {a s : State} (h : Sib X a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.1.2.2.2.2.1.symm

theorem Sib.e {a s : State} (h : Sib X a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.1.2.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib X a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

def At (X J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib X a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib X a s → f s = f a) {a t₁ t₂ : State} (h₁ : At X J a t₁) (h₂ : At X J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Sib X a s → f s = f a) :
    ∀ a t₁ t₂, At X J a t₁ → At X J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, PreS s → J s t → t.gpr .rsp = fb s) :
    Pins (At X J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1.1 j₁, hJ _ _ S₂.1.1 j₂, S₁.fb, S₂.fb]

theorem at_and {J : State → State → Prop} {P : State → Prop} {a t : State} (h : At X J a t ∧ P t) :
    At X (fun s t => J s t ∧ P t) a t :=
  let ⟨⟨s, S, j⟩, p⟩ := h; ⟨s, S, j, p⟩

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (At X fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => At X J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, at_and h₁, at_and h₂⟩) fun _ _ h => h

/-! ## The points of the code -/

def JA (s t : State) : Prop := t = allocState frameBytes s

def J1 (s t : State) : Prop :=
  Env s t ∧ t.gpr .r8 = off (fb s) oEM ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧ t.gpr .r9 = stackArg s 2

/-- The encoding of the hash value, as the entry state gives it. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId ((stackArg s 0).setWidth 32) (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (s.gpr .rcx).toNat

/-- Whether the encoding succeeds depends on the hash value's length alone. -/
theorem encodeId_isSome {x : BitVec 32} {H H' : List Byte} {k : Nat} (h : H.length = H'.length) :
    (encodeId x H k).isSome = (encodeId x H' k).isSome := by
  unfold encodeId
  split
  · simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, h]
    split <;> rfl
  · rfl

theorem encOut_sib {a s : State} (S : Sib X a s) : (encOut s).isSome = (encOut a).isSome := by
  unfold encOut
  rw [S.h, S.gpr (r := .rcx) (by decide)]
  exact encodeId_isSome (by rw [bytesAt_length, bytesAt_length, S.arg (by decide) (by decide)])

def J2 (s t : State) : Prop := ∃ t₁, J1 s t₁ ∧ Keep clob t₁ t ∧ EOut t₁ t (encOut s)

def J3 (s t : State) : Prop := ∃ t₂, J2 s t₂ ∧ SameF t₂ t ∧ t.zf = some !(encOut s).isSome

theorem J3_env {s t : State} (hp : PreS s) (h : J3 s t) : Env s t := by
  obtain ⟨t₂, ⟨t₁, ⟨he₁, h8₁, -⟩, hK, hout⟩, hs, -⟩ := h
  have hk2 := hp.k2
  have he₂ : Env s t₂ := by
    cases ho : encOut s with
    | none =>
      rw [ho] at hout
      exact he₁.regs (by rw [hK.gpr (by decide)]) hout.2 hK.2.1 hK.2.2
    | some em =>
      rw [ho] at hout
      have hl : em.length = (s.gpr .rcx).toNat := encodeId_length ho
      exact Env.of he₁ hp (hK.gpr (by decide)) hK.2.1 hK.2.2 (hout.2 ▸ frame_writeBytes _ _ _)
        fun r hr => .inl ⟨oEM, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₁, hl],
          .inr (Nat.le_refl _), by unfold oEM frameBytes; omega_using [hk2]⟩
  exact he₂.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2

theorem J3_rsp {s t : State} (h : J3 s t) : t.gpr .rsp = fb s := by
  obtain ⟨t₂, ⟨t₁, ⟨he₁, -⟩, hK, -⟩, hs, -⟩ := h
  rw [hs.1, hK.gpr (by decide), he₁.rsp]

def J6 (s t : State) : Prop :=
  t.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ t.gpr .r10 = off (fb s) oEM

/-! ## The call -/

theorem entryBytes {s t : State} (he : EnvC s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr, below_kb]; exact .inl (Region.sub_prefix (by decide))) hk ho hs hl

theorem callArg_sib {a s : State} (S : Sib X a s) {i : Nat} (hi : i < 14) : callArg s i = callArg a i := by
  match i, hi with
  | 0, _ => show off (fb s) oEM = off (fb a) oEM; rw [S.fb]
  | 1, _ => exact S.gpr (by decide)
  | j + 2, hj => exact S.arg (by omega_using []) (by omega_using [hj])

/-- What `vg_rsa_private_checked`'s contract makes public, of a call that
reads `rds`. -/
theorem privView_of {a s t : State} {rds : List Region} (S : Sib X a s) (he : EnvC s t)
    (hw : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rds (privWr s)).gpr =
      [a.gpr .rdi, a.gpr .rsi, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    (List.range 14).map (stackArg (t.callEntry.withRegions rds (privWr s))) =
      (List.range 14).map (callArg a) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions rds (privWr s)).mem
      ((t.callEntry.withRegions rds (privWr s)).gpr .rdx)
      ((t.callEntry.withRegions rds (privWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions rds (privWr s)).mem
      ((t.callEntry.withRegions rds (privWr s)).gpr .r8)
      ((t.callEntry.withRegions rds (privWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  have hp := S.1.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rsi) (by decide), S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [stackArg_entry he.rsp _ _ (by omega_using [hi]), hw i hi, callArg_sib S hi]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [entryBytes he _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_using []), S.n]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes he _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega_using []), S.e]

/-! ## The pieces -/

theorem head_two : RelCT isa (Two (At X JA)) (.block (slotStores ++ encArgs)) (Two (At X J1)) :=
  two_piece [.rsp] (pins_rsp fun s t _ h => by rw [show t = _ from h]; rfl) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = _ from ht]
      exact WP.mono (head_ok (S.1.1)) fun _ ⟨he, h8, hcx, hdx, hsi, h9, _⟩ =>
        ⟨s, S, he, h8, hcx, hdx, hsi, h9⟩

theorem encode_two : RelCT isa (Two (At X J1)) encode (Two (At X J2)) :=
  two_piece [.rsp, .r8, .rcx, .rdx, .rsi, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact pin fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
      · exact pin (fun s => off (fb s) oEM) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
      · exact pin (fun s => ((stackArg s 0).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
          (fun _ _ S => by rw [S.h]) h₁ h₂
      · exact pin (fun s => stackArg s 1) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.arg (by decide) (by decide))
          h₁ h₂
      · exact pin (fun s => stackArg s 2) (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.arg (by decide) (by decide))
          h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, j⟩ => by
      obtain ⟨he, h8, hcx, hdx, hsi, h9⟩ := j
      have hp := S.1.1
      refine WP.mono (encode_ok (encPre hp he h8 hcx hdx hsi h9)) fun u ⟨hK, hout⟩ =>
        ⟨s, S, t, ⟨he, h8, hcx, hdx, hsi, h9⟩, hK, ?_⟩
      have hH : Spec.Rsa.bytesAt t.mem (t.gpr .rsi) (t.gpr .r9).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat := by
        rw [hsi, h9]
        exact bytes_of_frame he.mem hp.dKd hp.dOd hp.dds.symm (by have := hp.wD; omega_using [])
      rw [hH] at hout
      exact hout

theorem test0_two : RelCT isa (Two (At X J2)) (.block test0) (Two (At X J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, j⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ => ⟨s, S, t, j, hs, by
      obtain ⟨t₁, -, -, hout⟩ := j
      rw [hz]
      cases h : encOut s with
      | none => rw [h] at hout; rw [hout.1]; rfl
      | some em => rw [h] at hout; rw [hout.1]; rfl⟩

def JZ (s t : State) : Prop := t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi

theorem zeroSlots_ct {J : State → State → Prop} (hJ : ∀ s t, PreS s → J s t → Env s t) :
    RelCT isa (Two (At X J)) zeroSlots fun _ _ => True := by
  unfold zeroSlots
  refine RelCT.seq (two_piece [.rsp] (pins_rsp fun s t hs h => (hJ s t hs h).rsp) (by taint_decide)
    (Ψ := At X JZ) fun _ t ⟨s, S, h⟩ => WP.mono (zeroHead_ok (S.1.1) (hJ s t S.1.1 h))
      fun _ ⟨_, _, hdi, hsi⟩ => ⟨s, S, hdi, hsi⟩) (Rec.zeroOut_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

def J5 (s t : State) : Prop := EnvC s t

theorem wipe_ct : RelCT isa (Two (At X J5)) wipe fun _ _ => True := by
  unfold wipe
  refine RelCT.seq (two_piece [.rsp] (pins_rsp fun _ _ _ h => h.rsp) (by taint_decide)
    (Ψ := At X J6) fun _ t ⟨s, S, he⟩ => WP.mono (wipeHead_ok (S.1.1) he)
      fun _ ⟨_, _, h11, _, h10⟩ => ⟨s, S, h11, h10⟩) (wipeLoop_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pin (fun s => off (fb s) oEM) (fun _ _ h => h.2) (fun _ _ S => by rw [S.fb]) h₁ h₂
  · exact pin (fun s => BitVec.ofNat 64 (s.gpr .rcx).toNat) (fun _ _ h => h.1)
      (fun _ _ S => by rw [S.gpr (r := .rcx) (by decide)]) h₁ h₂

/-! ## The composition -/

/-! ## The frame -/

theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) : s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_push p₁
      obtain rfl := alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

def J0 (s t : State) : Prop := t = s

/-! ## `Verified` -/

/-! ## Without secret residue

`vg_rsa_pkcs1_sign`'s registration scrubs it with `X86_64.Scrub.withScrubAll`,
which clears the registers its code writes and wipes all the stack its
frames and calls use: the residue analysis (`X86_64.RTaint`) does not follow
its code, so nothing of that stack is kept. This is what that needs of the
contract. -/

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
