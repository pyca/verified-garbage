module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreTop
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreTop
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.ScanTiming
meta import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
meta import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key_precompute` on i686 in time that depends on the domain only

The contract releases the domain. The recognition's scan branches on the
domain and the table (`VettedValidation.scan_ct`); the width's loop and
branches, and the table's squares, are related by their public counts; the
rest the taint analysis checks from the arguments.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute
open VG.Impl.Ffdh.X86 (tbOff ldOff tOff)

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {sp : BitVec 32}

/-! ## The recognition -/

/-- A run the recognition starts from, with the public domain `D` and the table at `T`. -/
structure RP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (dlen : Nat) (D : List Byte) (T : BitVec 32) (x : State) : Prop where
  inp : In Ex base bytes len args x
  geo : DomGeo args base bytes len dlen x.rd x.wr
  b40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  sym : x.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T
  tfit : T.toNat + 17744 ≤ 2 ^ 32
  tread : InRegions (x.rd ++ x.wr) (byteAddr T) 17744
  tbytes : Spec.Rsa.bytesAt x.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes
  tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩
  t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below sp 96)
  esp : x.gpr .esp = sp
  dom : Spec.Rsa.bytesAt x.mem (byteAddr (args 2)) dlen = D

theorem recognize_trace {dlen : Nat} {D : List Byte} {T : BitVec 32} :
    RelCT isa (Both (RP Ex base bytes len args sp dlen D T)) recognize fun _ _ => True := by
  unfold recognize
  -- `ebx := edi`.
  let PA : State → Prop := fun x => ∃ s, RP Ex base bytes len args sp dlen D T s ∧ Upd s x .ebx (s.gpr .edi)
  have A : RelCT isa (Both (RP Ex base bytes len args sp dlen D T)) (.block [.mov .ebx (.reg .edi)]) (Both PA) :=
    relCT_both (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block []) (by rfl))
      fun x hx => wp_movS rfl fun x' U _ => WP.block_nil ⟨x, hx, U⟩
  -- The table's address.
  let PB : State → Prop := fun x => ∃ s y, RP Ex base bytes len args sp dlen D T s ∧ Upd s y .ebx (s.gpr .edi) ∧
    SymAddrPost VG.Impl.Ffdh.X86.VettedValidation.tableSym y x
  have low : ∀ {x : State}, PA x → 4 ≤ (x.gpr .esp).toNat := fun ⟨s, P, U⟩ => by
    rw [U.other _ (by decide)]; have := P.inp.room.low; omega
  have B : RelCT isa (Both PA) VG.Impl.Ffdh.X86.VettedValidation.tableAddress (Both PB) := by
    refine relCT_both (fun x y tx ty x' y' h ex ey => ?_) fun x hx => ?_
    · obtain ⟨⟨s₁, P₁, U₁⟩, ⟨s₂, P₂, U₂⟩⟩ := h
      rw [symFrame_trace (low ⟨s₁, P₁, U₁⟩) ex, symFrame_trace (low ⟨s₂, P₂, U₂⟩) ey, U₁.other _ (by decide),
        U₂.other _ (by decide), P₁.esp, P₂.esp]
      exact ⟨rfl, trivial⟩
    · obtain ⟨s, P, U⟩ := hx
      exact WP.mono (symFrame_ok _ x (low ⟨s, P, U⟩)) fun x' R => ⟨s, x, P, U, R⟩
  -- To the header.
  let PC : State → Prop := fun x => ∃ s, RP Ex base bytes len args sp dlen D T s ∧ RH Ex base bytes len args T s x
  have C : RelCT isa (Both PB) (.block VG.Impl.Ffdh.X86.VettedValidation.saveTable) (Both PC) := by
    refine relCT_both (RelCT.taint (A := taint) (τr [.ebx]) (fun x y h => agree_regs fun r hr => ?_)
      (hc := .block []) (by rfl)) fun x ⟨s, y, P, U, R⟩ => WP.mono (saveTable_ok P.inp U R) fun x' M =>
        ⟨s, P, rh_of P.inp P.sym U R M⟩
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨⟨s₁, y₁, P₁, U₁, R₁⟩, ⟨s₂, y₂, P₂, U₂, R₂⟩⟩ := h
    rw [R₁.gpr _ (by decide), R₂.gpr _ (by decide), U₁.gpr, U₂.gpr, ← P₁.inp.edi_eq, ← P₂.inp.edi_eq]
  -- The scan, in its frame.
  have fit : 0 + (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, VG.Impl.Ffdh.VettedGroups.tableBytes] using
      Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  have valid : ∀ g ∈ VG.Impl.Ffdh.VettedGroups.groups, g.len < 2 ^ 32 := by
    intro g hg
    simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  let SC : State → Prop := fun w =>
    VettedValidation.Context (args 16) (args 2) (sp - BitVec.ofNat 32 16) T len D w ∧
      VettedValidation.TableAt (byteAddr T + BitVec.ofNat 64 0) VG.Impl.Ffdh.VettedGroups.groups w
  have scanArgsCT : RelCT isa (fun a b => ∃ s₁ s₂, Both PC s₁ s₂ ∧ a = allocFrame 16 s₁ ∧ b = allocFrame 16 s₂)
      (.block scanArgs) (Both SC) := by
    refine ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (hc := .block [])
      (by rfl)).wp (F₁ := SC) (F₂ := SC) fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    · obtain rfl := List.mem_singleton.mp hr
      obtain ⟨s₁, s₂, ⟨⟨x₁, P₁, H₁⟩, ⟨x₂, P₂, H₂⟩⟩, rfl, rfl⟩ := h
      rw [allocFrame_esp, allocFrame_esp, H₁.sp, H₂.sp, P₁.esp, P₂.esp]
    · obtain ⟨s₁, s₂, ⟨⟨x₁, P₁, H₁⟩, ⟨x₂, P₂, H₂⟩⟩, rfl, rfl⟩ := h
      have w : ∀ {x s : State}, RP Ex base bytes len args sp dlen D T x → RH Ex base bytes len args T x s →
          WP isa (.block scanArgs) (allocFrame 16 s) SC := fun {x s} P H => by
        have e := P.esp
        refine WP.mono (scanCtx_ok P.inp P.geo (by rw [e]; exact P.b40) P.tfit P.tread P.tbytes P.tws
          (by rw [e]; exact P.t40) H) fun w ⟨Cw, TA, _⟩ => ?_
        rw [e, P.dom] at Cw
        exact ⟨Cw, TA⟩
      exact ⟨w P₁ H₁, w P₂ H₂⟩
  have scanCT : RelCT isa (Both SC) (VG.Impl.Ffdh.X86.VettedValidation.scan VG.Impl.Ffdh.VettedGroups.groups 0)
      fun _ _ => True :=
    VettedValidation.scan_ct (base := args 16) (src := args 2) (sp := sp - BitVec.ofNat 32 16) (table := T)
      (k := len) (dom := D) _ 0 fit valid
  let PD : State → Prop := fun t => ∃ s x, RP Ex base bytes len args sp dlen D T s ∧ RH Ex base bytes len args T s x ∧
    Keeps [.eax, .ecx, .edx, .esi, .edi, .ebp] x t
  have Dct : RelCT isa (Both PC) (.frame (.alloc 16) (.seq (.block scanArgs)
      (VG.Impl.Ffdh.X86.VettedValidation.scan VG.Impl.Ffdh.VettedGroups.groups 0)) (.free 16)) (Both PD) :=
    relCT_both (RelCT.frameAlloc (R := fun _ _ => True) (VG.RelCT.seq scanArgsCT scanCT)) fun x ⟨s, P, H⟩ => by
      have e := P.esp
      exact WP.mono (recScan_ok P.inp P.geo (by rw [e]; exact P.b40) P.tfit P.tread P.tbytes P.tws
        (by rw [e]; exact P.t40) H) fun t ⟨_, _, _, _, _, K⟩ => ⟨s, x, P, H, K⟩
  -- `edi` back, the width to the header.
  have E : RelCT isa (Both PD) (.block [.mov .edi (.reg .ebx), .store (sc recOff) .eax]) fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebx]) (fun x y h => agree_regs fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      obtain ⟨⟨s₁, x₁, P₁, H₁, K₁⟩, ⟨s₂, x₂, P₂, H₂, K₂⟩⟩ := h
      rw [K₁.1 _ (by decide), K₂.1 _ (by decide), H₁.ebx, H₂.ebx, ← P₁.inp.edi_eq, ← P₂.inp.edi_eq])
      (hc := .block []) (by rfl)
  exact VG.RelCT.seq A (VG.RelCT.seq B (VG.RelCT.seq C (VG.RelCT.seq Dct E)))

end

end VG.Proof.Ffdh.X86.Cached
