module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Bignum.ReverseEncoding

/-! ### `RsaKeyGen.X86.ImportEncoding`, which the modules that import this one used -/

section

/-! # Whole-word reversal imports the exact big-endian candidate or witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont

theorem bswap_byte (x : BitVec 32) {k : Nat} (index : k < 4) :
    (bswap x).extractLsb' (8 * k) 8 = x.extractLsb' (8 * (3 - k)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  change ((byteRev32 x).extractLsb' (8 * k) 8).getLsbD i = _
  simp only [BitVec.getLsbD_extractLsb', bound, decide_true, Bool.true_and]
  rw [byteRev32_getLsbD _ (by omega_using [index, bound])]
  congr 1
  omega_using [bound]

theorem StateAt.bytes {g : Geometry} {s₀ s : State} (S : StateAt g s₀ g.count s)
    {j : Nat} (index : j < 4 * g.count) :
    s.mem (off (g.dst.setWidth 64) j) =
      s₀.mem (off (g.src.setWidth 64) (4 * g.count - 1 - j)) := by
  let word := g.count - 1 - j / 4
  have wi : word < g.count := by dsimp only [word]; omega_using [index]
  have k : j % 4 < 4 := Nat.mod_lt _ (by decide)
  have outAddr : off (g.dst.setWidth 64) j = g.destAt word + BitVec.ofNat 64 (j % 4) := by
    unfold Geometry.destAt off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    dsimp only [word]
    omega_using [index]
  have inAddr : off (g.src.setWidth 64) (4 * g.count - 1 - j) =
      g.sourceAt word + BitVec.ofNat 64 (3 - j % 4) := by
    unfold Geometry.sourceAt off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    dsimp only [word]
    omega_using [index]
  rw [outAddr, inAddr, Mem.readW_byte s.mem (g.destAt word) k, S.copied word wi, bswap_byte _ k,
    ← Mem.readW_byte s₀.mem (g.sourceAt word) (by omega_using [] : 3 - j % 4 < 4)]

theorem StateAt.os2ip {g : Geometry} {s₀ s : State} (S : StateAt g s₀ g.count s) :
    (s.mem.read (g.dst.setWidth 64) (4 * g.count)).toNat =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (g.src.setWidth 64) (4 * g.count)) :=
  VG.Proof.Bignum.reversed_read _ _ _ _ _ (fun _ index => S.bytes index)

end VG.Proof.RsaKeyGen.X86.Import

end

end

/-! ### `RsaKeyGen.X86.ImportState`, which only this module used -/

section

/-! # Each native import step extends the reversed-word prefix -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ImportStep.lean`, which only this module imported.
section

/-! # Exact effects of one native-word big-endian import -/

section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Import

theorem decrement {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .ecx (s.gpr .ecx - 1) →
      t.zf = some (s.gpr .ecx - 1 == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub .ecx (.imm 1) :: is)) s Q :=
  cons (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem step_ok (s : State) (src dst : Addr)
    (source : s.ea (at_ .esi) = src) (destination : s.ea (at_ .ebx) = dst)
    (readable : InRegions (s.rd ++ s.wr) src 4) (writable : InRegions s.wr dst 4) :
    WP isa (.block step) s fun t =>
      t.mem = s.mem.writeW dst (bswap (s.mem.readW src 32)) ∧
      t.gpr .esi = s.gpr .esi + 4 ∧ t.gpr .ebx = s.gpr .ebx - 4 ∧
      t.gpr .ecx = s.gpr .ecx - 1 ∧ t.zf = some (s.gpr .ecx - 1 == 0) ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  unfold step
  refine wp_movS (by change s.load32 (s.ea (at_ .esi)) = _; rw [source, State.load32,
    ite_eq_left_iff.mpr (fun h => absurd readable h)]) fun a A _ => ?_
  refine wp_bswap fun b B => ?_
  refine wp_storeS (a := dst)
    (by change (b.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = dst
        rw [B.other .ebx (by decide), A.other .ebx (by decide)]; exact destination)
    (by rw [B.wr, A.wr]; exact writable) fun c C => ?_
  refine wp_addS rfl fun d D _ => wp_subS rfl fun e E _ => decrement fun t T Z => WP.block_nil ?_
  have Kc := C.keeps []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem, B.gpr, A.gpr]
  · rw [T.other .esi (by decide), E.other .esi (by decide), D.gpr,
      Kc.1 .esi (by decide), B.other .esi (by decide), A.other .esi (by decide)]
  · rw [T.other .ebx (by decide), E.gpr, D.other .ebx (by decide), Kc.1 .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
  · rw [T.gpr, E.other .ecx (by decide), D.other .ecx (by decide), Kc.1 .ecx (by decide),
      B.other .ecx (by decide), A.other .ecx (by decide)]
  · rw [Z, E.other .ecx (by decide), D.other .ecx (by decide), Kc.1 .ecx (by decide),
      B.other .ecx (by decide), A.other .ecx (by decide)]
  · exact (((((A.keeps.mono (by decide)).widen B.keeps).widen Kc).widen D.keeps).widen E.keeps).widen T.keeps

end VG.Proof.RsaKeyGen.X86.Import
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Import

theorem StateAt.step {g : Geometry} {s₀ s : State} (C : Context g s₀) {i : Nat}
    (S : StateAt g s₀ i s) (index : i < g.count) :
    WP isa (.block step) s fun t => StateAt g s₀ (i + 1) t ∧ t.zf = some (decide (i + 1 = g.count)) := by
  have source : s.ea (at_ .esi) = g.sourceAt i := by
    change addr (s.gpr .esi) 0 = _
    rw [S.source]
    exact source_address C index
  have destination : s.ea (at_ .ebx) = g.destAt i := by
    change addr (s.gpr .ebx) 0 = _
    rw [S.destination]
    exact dest_address C index
  have hr := C.readable i index
  have hw := C.writable i index
  rw [← S.keeps.2.1, ← S.keeps.2.2] at hr
  rw [← S.keeps.2.2] at hw
  refine WP.mono (step_ok s _ _ source destination hr hw) fun t ⟨M, Ps, Pd, Pc, Z, K⟩ => ?_
  have input : s.mem.readW (g.sourceAt i) 32 = s₀.mem.readW (g.sourceAt i) 32 :=
    S.frame.readW (r := g.sourceRegion) (w := 32)
      (Offset.contains_base _ (by omega_using [index]) (by have := C.sourceFit; omega_using [index, this]))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.separate) (by decide)
  refine ⟨⟨by omega_using [index], ?_, ?_, ?_, ?_, ?_, S.keeps.trans K⟩, ?_⟩
  · rw [Ps, S.source]
    unfold Geometry.sourcePtr
    rw [BitVec.add_assoc]
    change g.src + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega_using []]
  · rw [Pd, S.destination]
    unfold Geometry.destPtr
    rw [BitVec.sub_sub]
    change _ - (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega_using []]
  · rw [Pc, S.count]
    change BitVec.ofNat 32 (g.count - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [index])]
    congr 1
  · intro j copied
    rw [M]
    by_cases same : j = i
    · subst j
      rw [Mem.readW_writeW_self32, input]
    · have sep : Mem.Sep (g.destAt j) 4 (g.destAt i) 4 := by
        apply Offset.sep (g.dst.setWidth 64)
        · omega_using [index, copied, same]
        · have := C.destFit; omega_using [this]
        · have := C.destFit; omega_using [this]
      rw [Mem.readW_writeW_sep sep (by decide)]
      exact S.copied j (by omega_using [copied, same])
  · rw [M]
    exact S.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [index]) (by have := C.destFit; omega_using [this]))
  · rw [Z, S.count]
    change some (BitVec.ofNat 32 (g.count - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [index]),
      ofNat_beq_zero (by have := C.sourceFit; omega_using [this])]
    simp only [show g.count - i - 1 = 0 ↔ i + 1 = g.count by omega_using [index]]

end VG.Proof.RsaKeyGen.X86.Import

end

end


/-! # A complete candidate or witness import, with exact reversed words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Import

theorem code_ok {g : Geometry} {s : State} (C : Context g s)
    (source : s.gpr .esi = g.sourcePtr 0) (destination : s.gpr .ebx = g.destPtr 0)
    (count : s.gpr .ecx = BitVec.ofNat 32 g.count) :
    WP isa code s (StateAt g s g.count) := by
  let Inv := fun q t => ∃ i, i + q = g.count ∧ 0 < q ∧ StateAt g s i t
  unfold code
  refine WP.loop (M := isa) Inv ?_ g.count s ?_
  · rintro q t ⟨i, iq, positive, T⟩
    refine WP.mono (T.step C (by omega_using [iq, positive])) fun u ⟨U, Z⟩ => ?_
    by_cases done : i + 1 = g.count
    · left
      refine ⟨?_, done ▸ U⟩
      change u.zf.map Bool.not = some false
      rw [Z, decide_eq_true done]
      rfl
    · right
      refine ⟨?_, q - 1, by omega_using [positive], i + 1, by omega_using [iq, positive], by omega_using [iq, positive, done], U⟩
      change u.zf.map Bool.not = some true
      rw [Z, decide_eq_false done]
      rfl
  · exact ⟨0, by omega_using [], C.positive, by omega_using [], source, destination,
      by simpa only [Nat.sub_zero] using count, by intro j h; omega, Frame.refl _ _, Keeps.refl _ _⟩

end VG.Proof.RsaKeyGen.X86.Import
