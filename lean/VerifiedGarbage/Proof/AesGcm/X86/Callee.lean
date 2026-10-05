import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Gcm.X86.Ghash
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Impl.AesGcm.X86
import VerifiedGarbage.Proof.Gcm.Be64

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.CT`. -/
section

/-!
# AES-GCM on x86: constant time, piece by piece

Untrusted: everything here is checked by Lean.

`CT I c`: any two runs of `c` from states satisfying `I` leak the same
trace. The AES-GCM pieces are proven constant time from their (public)
preconditions: every precondition of a piece is about public values (the
pointers, the lengths, `esp`), and what a piece computes from secrets is
stated in its postcondition as an implication from the memory it started
from, so the same `I` holds of both runs. The pieces are put together as the
code is (`CT.seq` takes the precondition of the second piece from the
correctness of the first, by determinism; `CT.ite` a condition that `I`
determines); straight-line code and loops without calls are proven by the
taint analysis, from the registers `I` pins (`CT.taint`), and each call in a
frame of its arguments by the callee's own proof (`CT.callWith`).
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86

/-- Two runs of `c` from states satisfying `I` leak the same trace. -/
def CT (I : VG.X86.State → Prop) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => I s₁ ∧ I s₂) c fun _ _ => True

namespace CT

theorem mono {I I' : VG.X86.State → Prop} {c : Prog isa} (h : VG.Proof.AesGcm.X86.CT I c) (hi : ∀ s, I' s → I s) : VG.Proof.AesGcm.X86.CT I' c :=
  RelCT.mono h (fun _ _ h => ⟨hi _ h.1, hi _ h.2⟩) fun _ _ _ => trivial

theorem seq {I J : VG.X86.State → Prop} {c₁ c₂ : Prog isa} (h₁ : VG.Proof.AesGcm.X86.CT I c₁) (hw : ∀ s, I s → WP isa c₁ s J)
    (h₂ : VG.Proof.AesGcm.X86.CT J c₂) : VG.Proof.AesGcm.X86.CT I (.seq c₁ c₂) :=
  have h₁' : RelCT isa (fun a b => I a ∧ I b) c₁ fun a b => J a ∧ J b :=
    RelCT.mono (RelCT.wp h₁ (F₁ := J) (F₂ := J) fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩) (fun _ _ h => h)
      fun _ _ h => h.2
  RelCT.seq h₁' h₂

theorem ite {I : VG.X86.State → Prop} {c : Cond} {t e : Prog isa} (b : Bool)
    (hc : ∀ s, I s → isa.eval c s = some b) (ht : b = true → VG.Proof.AesGcm.X86.CT I t) (he : b = false → VG.Proof.AesGcm.X86.CT I e) :
    VG.Proof.AesGcm.X86.CT I (.ite c t e) := by
  refine RelCT.ite (fun s₁ s₂ h => by rw [hc _ h.1, hc _ h.2]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun s₁ _ h => by rw [hc _ h.1.1] at h; simp at h
    · exact RelCT.mono (ht rfl) (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact RelCT.mono (he rfl) (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun s₁ _ h => by rw [hc _ h.1.1] at h; simp at h

/-- Code the taint analysis proves constant time from the registers `rs`, on
which any two states satisfying `I` agree. -/
theorem taint {I : VG.X86.State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) c hc).isSome = true) : VG.Proof.AesGcm.X86.CT I c :=
  RelCT.taint (A := VG.X86.taint) (τr rs) (fun _ _ hp => agree_regs (hr _ _ hp.1 hp.2)) h

/-- A call of verified code in a frame of its arguments. -/
theorem callWith {I : VG.X86.State → Prop} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : List Region)
    (hP : ∀ s₁ s₂, I s₁ → I s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    VG.Proof.AesGcm.X86.CT I (.frame (.push rs) (.call n c) (.pop .eax rs.length)) :=
  RelCT.callWith hv hct rd wr fun _ _ h => hP _ _ h.1 h.2

theorem nil {I : VG.X86.State → Prop} : VG.Proof.AesGcm.X86.CT I (.block []) := RelCT.nil fun _ _ _ => trivial

/-- Cases on a public value. -/
theorem cases {α : Sort _} {I : α → VG.X86.State → Prop} {c : Prog isa} (h : ∀ a, VG.Proof.AesGcm.X86.CT (I a) c)
    (hu : ∀ a b s₁ s₂, I a s₁ → I b s₂ → a = b) : VG.Proof.AesGcm.X86.CT (fun s => ∃ a, I a s) c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨a, h₁⟩, ⟨b, h₂⟩⟩ e₁ e₂
  obtain rfl := hu a b s₁ s₂ h₁ h₂
  exact h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

end CT

/-- Constant time of a whole function, from `CT` for each value of what is
public (`f`). -/
theorem CT.constantTime {α : Sort _} {Pre : VG.X86.State → Prop} {Pub : VG.X86.State → VG.X86.State → Prop} {c : Prog isa}
    (f : VG.X86.State → α) (hf : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → f s₁ = f s₂)
    (h : ∀ a, VG.Proof.AesGcm.X86.CT (fun s => Pre s ∧ f s = a) c) : ConstantTime isa Pre Pub c :=
  fun s₁ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (h (f s₁) _ _ _ _ _ _ ⟨⟨h₁, rfl⟩, ⟨h₂, (hf _ _ h₁ h₂ hp).symm⟩⟩ e₁ e₂).1

/-! ## Pieces: correctness and constant time together

`Pc P c Q`: from a state satisfying `P a`, `c` ends in one satisfying `Q a`,
and any two runs from states satisfying `P a` and `P b` leak the same
trace. The index `a` is what is secret about the run (the memory it starts
from, say): it may differ between the two runs; everything `P` says of the
registers the code branches on or addresses memory with must not depend on
it. -/

structure Pc {α : Sort _} (P : α → VG.X86.State → Prop) (c : Prog isa) (Q : α → VG.X86.State → Prop) : Prop where
  wp : ∀ a s, P a s → WP isa c s (Q a)
  ct : VG.Proof.AesGcm.X86.CT (fun s => ∃ a, P a s) c

namespace Pc

variable {α : Sort _}

theorem mono {P P' Q Q' : α → VG.X86.State → Prop} {c : Prog isa} (h : VG.Proof.AesGcm.X86.Pc P c Q) (hp : ∀ a s, P' a s → P a s)
    (hq : ∀ a s, Q a s → Q' a s) : VG.Proof.AesGcm.X86.Pc P' c Q' :=
  ⟨fun a s hs => WP.mono (h.wp a s (hp a s hs)) (hq a), h.ct.mono fun _ ⟨a, h⟩ => ⟨a, hp a _ h⟩⟩

theorem seq {P Q R : α → VG.X86.State → Prop} {c₁ c₂ : Prog isa} (h₁ : VG.Proof.AesGcm.X86.Pc P c₁ Q) (h₂ : VG.Proof.AesGcm.X86.Pc Q c₂ R) :
    VG.Proof.AesGcm.X86.Pc P (.seq c₁ c₂) R :=
  ⟨fun a s hs => WP.seq (WP.mono (h₁.wp a s hs) fun s' h => h₂.wp a s' h),
    CT.seq h₁.ct (fun _ ⟨a, h⟩ => WP.mono (h₁.wp a _ h) fun _ h => ⟨a, h⟩) h₂.ct⟩

/-- A piece proven on its own, with a precondition `I` that `P` implies and a
postcondition relating the states before and after. -/
theorem of {I : VG.X86.State → Prop} {R : VG.X86.State → VG.X86.State → Prop} {c : Prog isa}
    (hw : ∀ s, I s → WP isa c s (R s)) (hct : VG.Proof.AesGcm.X86.CT I c) (P : α → VG.X86.State → Prop) (hP : ∀ a s, P a s → I s) :
    VG.Proof.AesGcm.X86.Pc P c fun a s' => ∃ s, P a s ∧ R s s' :=
  ⟨fun a s hs => WP.mono (hw s (hP a s hs)) fun _ h => ⟨s, hs, h⟩,
    hct.mono fun _ ⟨a, h⟩ => hP a _ h⟩

/-- A branch on a condition that `P` determines. -/
theorem ite {P Q : α → VG.X86.State → Prop} {c : Cond} {t e : Prog isa} (b : Bool)
    (hc : ∀ a s, P a s → isa.eval c s = some b) (ht : b = true → VG.Proof.AesGcm.X86.Pc P t Q) (he : b = false → VG.Proof.AesGcm.X86.Pc P e Q) :
    VG.Proof.AesGcm.X86.Pc P (.ite c t e) Q := by
  refine ⟨fun a s hs => WP.ite b (hc a s hs) (fun h => (ht h).wp a s hs) (fun h => (he h).wp a s hs), ?_⟩
  exact CT.ite b (fun s ⟨a, h⟩ => hc a s h) (fun h => (ht h).ct) (fun h => (he h).ct)

/-- Code the taint analysis proves constant time from the registers `rs`, on
which `P` pins the same values whatever the index. -/
theorem taint {P Q : α → VG.X86.State → Prop} {c : Prog isa} (rs : List Reg) (hw : ∀ a s, P a s → WP isa c s (Q a))
    (hr : ∀ a b s₁ s₂, P a s₁ → P b s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) c hc).isSome = true) : VG.Proof.AesGcm.X86.Pc P c Q :=
  ⟨hw, CT.taint rs (fun _ _ ⟨a, h₁⟩ ⟨b, h₂⟩ => hr a b _ _ h₁ h₂) h⟩

theorem nil {P : α → VG.X86.State → Prop} : VG.Proof.AesGcm.X86.Pc P (.block []) P :=
  ⟨fun _ _ h => WP.block_nil h, CT.nil⟩

/-- A piece indexed by `α`, in code indexed by `β`: the index of the piece
from that of the code and the state it starts in. Its postcondition holds
of the state the piece started in, which has the permissions of the one it
ends in. -/
theorem lift {β : Sort _} {P : α → VG.X86.State → Prop} {Q : α → VG.X86.State → Prop} {c : Prog isa} (h : VG.Proof.AesGcm.X86.Pc P c Q)
    {P' : β → VG.X86.State → Prop} (f : β → VG.X86.State → α) (hP : ∀ b s, P' b s → P (f b s) s) :
    VG.Proof.AesGcm.X86.Pc P' c fun b s' => ∃ s, P' b s ∧ Q (f b s) s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨fun b s hs => ?_, h.ct.mono fun s ⟨b, hb⟩ => ⟨f b s, hP b s hb⟩⟩
  obtain ⟨t, s', he, hq⟩ := h.wp _ s (hP b s hs)
  exact ⟨t, s', he, s, hs, hq, Exec.rdwr he⟩

/-- Correctness and constant time of a whole function. -/
theorem constantTime {β : Sort _} {Pre : VG.X86.State → Prop} {Pub : VG.X86.State → VG.X86.State → Prop} {c : Prog isa}
    {P : β → VG.X86.State → VG.X86.State → Prop} {Q : β → VG.X86.State → VG.X86.State → Prop} (f : VG.X86.State → β)
    (hf : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → f s₁ = f s₂) (h : ∀ p, VG.Proof.AesGcm.X86.Pc (P p) c (Q p))
    (hp : ∀ s, Pre s → P (f s) s s) : ConstantTime isa Pre Pub c :=
  CT.constantTime f hf fun p => (h p).ct.mono fun s ⟨h₁, h₂⟩ => ⟨s, h₂ ▸ hp s h₁⟩

end Pc

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Callee`. -/
section

/-!
# AES-GCM on x86: the calls

Untrusted: everything here is checked by Lean. Each call of `vg_ghash`,
`vg_aes_ctr32` and `vg_aes_expand_key_scratch`, in a frame of its arguments, from
the callee's contract (`WP.callWith`): what it needs of the registers it
pushes and of the regions it is given (`GhCall`, `CtrCall`, `KeyCall`), and
what it leaves (`GhPost`, `CtrPost`, `KeyPost`), in terms of the memory
before the call; and that it is constant time (`gh_ct`, `ctr_ct`, `key_ct`)
by the callee's own proof, when the arguments are the same in both runs.
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-- The 64-bit address of a 32-bit pointer. -/
abbrev w64 (x : BitVec 32) : Addr := x.setWidth 64

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_add32 {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, VG.Proof.AesGcm.X86.toNat_ofNat32 (by omega), Nat.mod_eq_of_lt h]

theorem w64_add {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    VG.Proof.AesGcm.X86.w64 (x + BitVec.ofNat 32 k) = VG.Proof.AesGcm.X86.w64 x + BitVec.ofNat 64 k := addr_eq h

theorem toNat_w64 (x : BitVec 32) : (VG.Proof.AesGcm.X86.w64 x).toNat = x.toNat := by
  simp only [VG.Proof.AesGcm.X86.w64, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, VG.Proof.AesGcm.X86.bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, VG.Proof.AesGcm.X86.bytesAt_frame hf hd hn]

theorem one_disj {k : Region} {p : Addr} {n : Nat} (h : k.Disjoint ⟨p, n⟩) :
    ∀ r ∈ [k], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

/-! ## The callees -/

/-- An implementation of `vg_ghash` on x86. -/
structure GhashImpl where
  fn : Impl.AesGcm.X86.Fn
  stack : stackUse fn.code = 0
  ok : ∀ s, Proof.Gcm.ghashX86.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashX86.post s s'
  ct : ConstantTime isa Proof.Gcm.ghashX86.pre Proof.Gcm.ghashX86.pub fn.code
  nosp : NoSp fn.code
  spSafe : fn.code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : VG.Proof.AesGcm.X86.GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.X86.ghash⟩
  stack := by decide +kernel
  ok := Proof.Gcm.X86.ghash_correct
  ct := Proof.Gcm.X86.ghash_ct
  nosp := NoSp.of_all (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

end GhashImpl

/-- The implementations a set of AES-GCM functions calls: of
`vg_aes_ctr32` with its `vg_aes_expand_key_scratch` (`Ctr32Impl`), and of
`vg_ghash`. -/
structure GcmImpl where
  ctr : Proof.Aes.X86.Ctr32Impl
  gh : VG.Proof.AesGcm.X86.GhashImpl

namespace GcmImpl

variable (v : VG.Proof.AesGcm.X86.GcmImpl)

def callees : Callees :=
  ⟨⟨v.ctr.callee.name, v.ctr.callee.code⟩, ⟨v.ctr.expand.name, v.ctr.expand.code⟩, v.gh.fn⟩

/-- What the names of the functions calling them end with. -/
def suffix : String := v.ctr.suffix ++ v.gh.suffix

end GcmImpl

/-! ## `vg_ghash` -/

abbrev ghRegs : List Reg := [.ebp, .edi, .ebx, .edx, .eax]

theorem ghRegs_esp : Reg.esp ∉ VG.Proof.AesGcm.X86.ghRegs := by decide

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`. -/
structure GhCall (s : State) (H Y D S : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = H
  edx : s.gpr .edx = Y
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  esp : 24 ≤ (s.gpr .esp).toNat
  hy : (⟨VG.Proof.AesGcm.X86.w64 H, 16⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩
  hs : (⟨VG.Proof.AesGcm.X86.w64 H, 16⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩
  yd : (⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩
  ys : (⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩
  ds : (⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩
  kh : (below (s.gpr .esp) 24).Disjoint ⟨VG.Proof.AesGcm.X86.w64 H, 16⟩
  ky : (below (s.gpr .esp) 24).Disjoint ⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩
  kd : (below (s.gpr .esp) 24).Disjoint ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩
  ks : (below (s.gpr .esp) 24).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩
  fH : H.toNat + 16 ≤ 2 ^ 32
  fY : Y.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 256 ≤ 2 ^ 32
  reads : Covers [⟨VG.Proof.AesGcm.X86.w64 H, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : blockAt s'.mem (VG.Proof.AesGcm.X86.w64 Y) = ghashFrom (blockAt s.mem (VG.Proof.AesGcm.X86.w64 H)) (blockAt s.mem (VG.Proof.AesGcm.X86.w64 Y))
    (blocksAt s.mem (VG.Proof.AesGcm.X86.w64 D) n)

/-- The regions `vg_ghash` is called with. -/
abbrev ghRd (E H D : BitVec 32) (n : Nat) : List Region :=
  [⟨VG.Proof.AesGcm.X86.w64 H, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩, below E 20]
abbrev ghWr (Y S : BitVec 32) : List Region := [⟨VG.Proof.AesGcm.X86.w64 Y, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 256⟩]

namespace GhCall
variable {s : State} {H Y D S : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.X86.GhCall s H Y D S n)
include h

theorem fit : 4 * ghRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry 0 = H ∧ arg (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry 1 = Y ∧
    arg (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry 2 = D ∧ arg (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry 3 = BitVec.ofNat 32 n ∧
    arg (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.AesGcm.X86.ghRegs_esp (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.edi, h.ebp]

theorem sub20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 24) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 24) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 24) (k := 20) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Gcm.ghashX86 VG.Proof.AesGcm.X86.ghRegs (VG.Proof.AesGcm.X86.ghRd (s.gpr .esp) H D n) (VG.Proof.AesGcm.X86.ghWr Y S) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hn := VG.Proof.AesGcm.X86.toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.AesGcm.X86.ghRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Gcm.ghashX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hn]
    refine ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, h.ky.sub_left h.sub20,
      h.ks.sub_left h.sub20, h.ky.sub_left h.sub4, h.ks.sub_left h.sub4, h.fH, h.fY, h.fD, h.fS, ?_⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end GhCall

theorem gh_call (v : VG.Proof.AesGcm.X86.GcmImpl) {s : State} {H Y D S : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.X86.GhCall s H Y D S n) :
    WP isa (ghCall v.callees) s (VG.Proof.AesGcm.X86.GhPost s H Y D S n) := by
  have hn := VG.Proof.AesGcm.X86.toNat_ofNat32 h.n_lt
  unfold ghCall
  refine WP.callWith (rs := VG.Proof.AesGcm.X86.ghRegs) (k := Proof.Gcm.ghashX86) v.gh.ok v.gh.nosp (by simp)
    VG.Proof.AesGcm.X86.ghRegs_esp (by rw [v.gh.stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  rw [v.gh.stack] at f'
  have fE := callEntry_frame h.fit VG.Proof.AesGcm.X86.ghRegs_esp
  rw [show 4 * ghRegs.length + 4 = 24 from rfl] at fE
  simp only [Proof.Gcm.ghashX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hn, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [post, VG.Proof.AesGcm.X86.blockAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.kh), VG.Proof.AesGcm.X86.blockAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.ky),
      VG.Proof.AesGcm.X86.blocksAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.kd) (by have := h.fD; omega)]

/-- Calls of `vg_ghash` with the same arguments and stack pointer in both
runs are constant time. -/
theorem gh_ct (v : VG.Proof.AesGcm.X86.GcmImpl) {I : State → Prop} {H Y D S E : BitVec 32} {n : Nat}
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.GhCall s H Y D S n ∧ s.gpr .esp = E) : VG.Proof.AesGcm.X86.CT I (ghCall v.callees) := by
  refine CT.callWith v.gh.ok v.gh.ct (VG.Proof.AesGcm.X86.ghRd E H D n) (VG.Proof.AesGcm.X86.ghWr Y S)
    fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `vg_aes_ctr32` -/

abbrev ctrRegs : List Reg := [.ebp, .edi, .ebx, .edx, .ecx, .eax]

theorem ctrRegs_esp : Reg.esp ∉ VG.Proof.AesGcm.X86.ctrRegs := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R :=
  VG.Proof.AesGcm.X86.toNat_ofNat32 (by omega)

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 28 ≤ (s.gpr .esp).toNat
  kc : (⟨VG.Proof.AesGcm.X86.w64 K, 240⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 C, 16⟩
  kd : (⟨VG.Proof.AesGcm.X86.w64 K, 240⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩
  ks : (⟨VG.Proof.AesGcm.X86.w64 K, 240⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩
  cd : (⟨VG.Proof.AesGcm.X86.w64 C, 16⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩
  cs : (⟨VG.Proof.AesGcm.X86.w64 C, 16⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩
  ds : (⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩
  bk : (below (s.gpr .esp) 28).Disjoint ⟨VG.Proof.AesGcm.X86.w64 K, 240⟩
  bc : (below (s.gpr .esp) 28).Disjoint ⟨VG.Proof.AesGcm.X86.w64 C, 16⟩
  bd : (below (s.gpr .esp) 28).Disjoint ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩
  bs : (below (s.gpr .esp) 28).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩
  fK : K.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨VG.Proof.AesGcm.X86.w64 K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨VG.Proof.AesGcm.X86.w64 C, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨VG.Proof.AesGcm.X86.w64 C, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩, below (s.gpr .esp) 28] s.mem s'.mem
  out : blocksAt s'.mem (VG.Proof.AesGcm.X86.w64 D) n = ctr32 (aesWith R (bytesAt s.mem (VG.Proof.AesGcm.X86.w64 K) (16 * (R + 1))))
    (blockAt s.mem (VG.Proof.AesGcm.X86.w64 C)) (blocksAt s.mem (VG.Proof.AesGcm.X86.w64 D) n)
  ctr : blockAt s'.mem (VG.Proof.AesGcm.X86.w64 C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (VG.Proof.AesGcm.X86.w64 C))

abbrev ctrRd (E K : BitVec 32) : List Region := [⟨VG.Proof.AesGcm.X86.w64 K, 240⟩, below E 24]
abbrev ctrWr (C D S : BitVec 32) (n : Nat) : List Region :=
  [⟨VG.Proof.AesGcm.X86.w64 C, 16⟩, ⟨VG.Proof.AesGcm.X86.w64 D, 16 * n⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 2048⟩]

namespace CtrCall
variable {s : State} {K C D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesGcm.X86.CtrCall s K C D S R n)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 0 = K ∧ arg (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 2 = C ∧ arg (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 3 = D ∧
    arg (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 4 = BitVec.ofNat 32 n ∧ arg (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.AesGcm.X86.ctrRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.ctr32X86 VG.Proof.AesGcm.X86.ctrRegs (VG.Proof.AesGcm.X86.ctrRd (s.gpr .esp) K) (VG.Proof.AesGcm.X86.ctrWr C D S n) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := VG.Proof.AesGcm.X86.toNat_rounds h.rounds
  have hn := VG.Proof.AesGcm.X86.toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.AesGcm.X86.ctrRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.ctr32X86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hn]
    refine ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.bc.sub_left h.sub24,
      h.bd.sub_left h.sub24, h.bs.sub_left h.sub24, h.bc.sub_left h.sub4, h.bd.sub_left h.sub4,
      h.bs.sub_left h.sub4, h.fK, h.fC, h.fD, h.fS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end CtrCall

theorem ctr_call (v : VG.Proof.AesGcm.X86.GcmImpl) {s : State} {K C D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesGcm.X86.CtrCall s K C D S R n) :
    WP isa (ctrCall v.callees) s (VG.Proof.AesGcm.X86.CtrPost s K C D S R n) := by
  have hR := VG.Proof.AesGcm.X86.toNat_rounds h.rounds
  have hn := VG.Proof.AesGcm.X86.toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold ctrCall
  refine WP.callWith (rs := VG.Proof.AesGcm.X86.ctrRegs) (k := Proof.Aes.ctr32X86) v.ctr.ok v.ctr.nosp (by simp)
    VG.Proof.AesGcm.X86.ctrRegs_esp (by rw [v.ctr.stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [v.ctr.stack] at f'
  have fE := callEntry_frame h.fit VG.Proof.AesGcm.X86.ctrRegs_esp
  rw [show 4 * ctrRegs.length + 4 = 28 from rfl] at fE
  obtain ⟨hdata, hctr⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hn, m₂] at hdata hctr
  have eK := VG.Proof.AesGcm.X86.bytesAt_frame fE (p := VG.Proof.AesGcm.X86.w64 K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix hR')).symm) (by omega)
  rw [VG.Proof.AesGcm.X86.blockAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.bc), VG.Proof.AesGcm.X86.blocksAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.bd) (by have := h.fD; omega),
    eK] at hdata
  rw [VG.Proof.AesGcm.X86.blockAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.bc)] at hctr
  refine ⟨rd', wr', cs', ?_, hdata, hctr⟩
  exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of `vg_aes_ctr32` with the same arguments and stack pointer in
both runs are constant time. -/
theorem ctr_ct (v : VG.Proof.AesGcm.X86.GcmImpl) {I : State → Prop} {K C D S E : BitVec 32} {R n : Nat}
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.CtrCall s K C D S R n ∧ s.gpr .esp = E) : VG.Proof.AesGcm.X86.CT I (ctrCall v.callees) := by
  refine CT.callWith v.ctr.ok v.ctr.ct (VG.Proof.AesGcm.X86.ctrRd E K) (VG.Proof.AesGcm.X86.ctrWr C D S n)
    fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

/-! ## `vg_aes_expand_key_scratch` -/

abbrev keyRegs : List Reg := [.ebp, .edx, .ecx, .eax]

theorem keyRegs_esp : Reg.esp ∉ VG.Proof.AesGcm.X86.keyRegs := by decide

/-- What a call of `vg_aes_expand_key_scratch` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : BitVec 32) (L : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 L
  edx : s.gpr .edx = C
  ebp : s.gpr .ebp = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  esp : 20 ≤ (s.gpr .esp).toNat
  kc : (⟨VG.Proof.AesGcm.X86.w64 K, L⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 C, 240⟩
  ks : (⟨VG.Proof.AesGcm.X86.w64 K, L⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 512⟩
  cs : (⟨VG.Proof.AesGcm.X86.w64 C, 240⟩ : Region).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 512⟩
  bk : (below (s.gpr .esp) 20).Disjoint ⟨VG.Proof.AesGcm.X86.w64 K, L⟩
  bc : (below (s.gpr .esp) 20).Disjoint ⟨VG.Proof.AesGcm.X86.w64 C, 240⟩
  bs : (below (s.gpr .esp) 20).Disjoint ⟨VG.Proof.AesGcm.X86.w64 S, 512⟩
  fK : K.toNat + L ≤ 2 ^ 32
  fC : C.toNat + 240 ≤ 2 ^ 32
  fS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨VG.Proof.AesGcm.X86.w64 K, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨VG.Proof.AesGcm.X86.w64 C, 240⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure KeyPost (s : State) (K C S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨VG.Proof.AesGcm.X86.w64 C, 240⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 512⟩, below (s.gpr .esp) 20] s.mem s'.mem
  out : bytesAt s'.mem (VG.Proof.AesGcm.X86.w64 C) (16 * (Spec.Aes.rounds (L / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem (VG.Proof.AesGcm.X86.w64 K) L)

abbrev keyRd (E K : BitVec 32) (L : Nat) : List Region := [⟨VG.Proof.AesGcm.X86.w64 K, L⟩, below E 16]
abbrev keyWr (C S : BitVec 32) : List Region := [⟨VG.Proof.AesGcm.X86.w64 C, 240⟩, ⟨VG.Proof.AesGcm.X86.w64 S, 512⟩]

namespace KeyCall
variable {s : State} {K C S : BitVec 32} {L : Nat} (h : VG.Proof.AesGcm.X86.KeyCall s K C S L)
include h

theorem fit : 4 * keyRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem L_lt : L < 2 ^ 32 := by rcases h.len with h' | h' | h' <;> omega

theorem args : arg (pushed VG.Proof.AesGcm.X86.keyRegs s).callEntry 0 = K ∧ arg (pushed VG.Proof.AesGcm.X86.keyRegs s).callEntry 1 = BitVec.ofNat 32 L ∧
    arg (pushed VG.Proof.AesGcm.X86.keyRegs s).callEntry 2 = C ∧ arg (pushed VG.Proof.AesGcm.X86.keyRegs s).callEntry 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.AesGcm.X86.keyRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebp]

theorem sub16 : Region.Sub (below (s.gpr .esp) 16) (below (s.gpr .esp) 20) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below (s.gpr .esp) 20) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 20) (k := 16) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 20 = s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.expandKeyX86 VG.Proof.AesGcm.X86.keyRegs (VG.Proof.AesGcm.X86.keyRd (s.gpr .esp) K L) (VG.Proof.AesGcm.X86.keyWr C S) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hL := VG.Proof.AesGcm.X86.toNat_ofNat32 h.L_lt
  have eA : argAddr (pushed VG.Proof.AesGcm.X86.keyRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.AesGcm.X86.keyRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.expandKeyX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hL]
    refine ⟨trivial, trivial, h.kc, h.ks, h.cs, h.bc.sub_left h.sub16, h.bs.sub_left h.sub16,
      h.bc.sub_left h.sub4, h.bs.sub_left h.sub4, h.fK, h.fC, h.fS, ?_, h.len⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end KeyCall

theorem key_call (v : VG.Proof.AesGcm.X86.GcmImpl) {s : State} {K C S : BitVec 32} {L : Nat} (h : VG.Proof.AesGcm.X86.KeyCall s K C S L) :
    WP isa (keyCall v.callees) s (VG.Proof.AesGcm.X86.KeyPost s K C S L) := by
  have hL := VG.Proof.AesGcm.X86.toNat_ofNat32 h.L_lt
  unfold keyCall
  refine WP.callWith (rs := VG.Proof.AesGcm.X86.keyRegs) (k := Proof.Aes.expandKeyX86) v.ctr.expandOk v.ctr.expandNosp
    (by simp) VG.Proof.AesGcm.X86.keyRegs_esp (by rw [v.ctr.expandStack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [v.ctr.expandStack] at f'
  have fE := callEntry_frame h.fit VG.Proof.AesGcm.X86.keyRegs_esp
  rw [show 4 * keyRegs.length + 4 = 20 from rfl] at fE
  simp only [Proof.Aes.expandKeyX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hL, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [post, VG.Proof.AesGcm.X86.bytesAt_frame fE (VG.Proof.AesGcm.X86.one_disj h.bk) (by rcases h.len with rfl | rfl | rfl <;> decide)]

/-- Calls of `vg_aes_expand_key_scratch` with the same arguments and stack pointer
in both runs are constant time. -/
theorem key_ct (v : VG.Proof.AesGcm.X86.GcmImpl) {I : State → Prop} {K C S E : BitVec 32} {L : Nat}
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.KeyCall s K C S L ∧ s.gpr .esp = E) : VG.Proof.AesGcm.X86.CT I (keyCall v.callees) := by
  refine CT.callWith v.ctr.expandOk v.ctr.expandCt (VG.Proof.AesGcm.X86.keyRd E K L) (VG.Proof.AesGcm.X86.keyWr C S)
    fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

/-- The implementations of `vg_ghash`, by name, as the variants of `AesGcm`
choose them (`GcmVariant`). `GhashName.impl`, in `GhashImpls.lean`, gives
their `GhashImpl`s, whose proofs import the algebra of `Proof/Gcm/Poly.lean`,
which the variants then need not import. -/
inductive GhashName where
  | scalar
  | pclmul

/-- A variant of `AesGcm` (see `TCB/Emit.lean`): a `GcmImpl` with its
implementation of `vg_ghash` named (`GhashName`), which `GcmVariant.impl`
(`GhashImpls.lean`) resolves. -/
structure GcmVariant where
  ctr : Proof.Aes.X86.Ctr32Impl
  gh : VG.Proof.AesGcm.X86.GhashName

end VG.Proof.AesGcm.X86

end
