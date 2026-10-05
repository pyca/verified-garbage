import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Impl.MlKem.X86.Ntt
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Red`. -/
section

/-!
# ML-KEM on x86 (32-bit): Barrett reduction and products

`red r` reduces `x < 2³²`, held in `eax` and in `r`, modulo `q` (`red_spec`):
`barrett64` with the quotient estimate the high half of a `mul`, then
`condSub`. `mul r` multiplies (`wp_mul`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- `mul r` -/
theorem wp_mul {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (execMul r s) Q) : WP isa (.block (.mul r :: is)) s Q :=
  wp_cons rfl k

theorem execMul_eax (r : Reg) (s : State) :
    (execMul r s).gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) := by
  simp [execMul, State.setReg, State.setFlags]

theorem execMul_other (r : Reg) (s : State) {x : Reg} (h1 : x ≠ .eax) (h2 : x ≠ .edx) :
    (execMul r s).gpr x = s.gpr x := by
  simp [execMul, State.setReg, State.setFlags, h1, h2]

theorem execMul_only (r : Reg) (s : State) : Only [.eax, .edx] s (execMul r s) :=
  ⟨fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact VG.Proof.MlKem.X86.execMul_other r s hx.1 hx.2, rfl, rfl, rfl⟩

/-- `red r` leaves `x mod q` in `r` from `eax = r = x`, changing only `eax`, `edx`, `r` and the
flags. -/
theorem red_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (ha : (s.gpr .eax).toNat = x) (hr : (s.gpr r).toNat = x)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = x % q → WP isa (.block is) s' P) :
    WP isa (.block (red r ++ is)) s P := by
  have hx : x < 2 ^ 32 := by rw [← ha]; exact (s.gpr .eax).isLt
  have h2' : Reg.edx ≠ r := fun e => h2 e.symm
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, red, csub, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', h1, h2,
    h2']
  refine k _ ⟨fun q hq => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [hq.1, hq.2.1, hq.2.2]
  · simp only [ite_true]
    have hb := barrett64_bounds hx
    have hq1 : (BitVec.ofNat 32 (x * 1290167 / 2 ^ 32)).toNat = barrett64Quot x := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold barrett64Quot at *; omega)]; rfl
    have hm : (BitVec.ofNat 32 (3329 * barrett64Quot x)).toNat = barrett64Quot x * q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [q_eq] at hb; omega), q_eq, Nat.mul_comm]
    have e : (s.gpr r - BitVec.ofNat 32 ((3329 : BitVec 32).toNat *
        (BitVec.ofNat 32 ((s.gpr .eax).toNat * (1290167 : BitVec 32).toNat / 2 ^ 32)).toNat)).toNat =
        barrett64 x := by
      rw [ha, show (1290167 : BitVec 32).toNat = 1290167 from rfl, hq1,
        show (3329 : BitVec 32).toNat = 3329 from rfl]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hm, hr]; exact hb.2), hm, hr]
      rfl
    rw [csub_eq _ _ (by rw [e]; exact barrett64_lt hx), e, toNat_ofNat32 (by
      have := barrett64_lt hx; rw [q_eq] at this ⊢; omega), barrett64_mod hx]

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Bfly`. -/
section

/-!
# ML-KEM on x86 (32-bit): the butterflies

With `esi` at coefficient `j` and `edi` at coefficient `j + len` of a
polynomial `G` stored at `p` and `ebp` at a zeta `z` (`BIn`), `bflyBody`
leaves `bfly G j len z` there and `ibflyBody` leaves `bflyInv G j len z`
(`BOut`), both advancing `esi` and `edi` by 4 and counting `ecx` down.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- A butterfly's inputs. -/
structure BIn (s : State) (p : Addr) (G : Poly) (j len : Nat) (zA : Addr) (z : Nat) : Prop where
  ea_i : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p j
  ea_d : (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p (j + len)
  ea_z : (s.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = zA
  in_i : InRegions s.wr (coeffAddr p j) 4
  in_d : InRegions s.wr (coeffAddr p (j + len)) 4
  in_z : InRegions (s.rd ++ s.wr) zA 4
  z_v : s.mem.readW zA 32 = BitVec.ofNat 32 z
  z_lt : z < q
  z_sep : Mem.Sep zA 4 (coeffAddr p j) 4
  poly : PolyIs s.mem p G
  hj : j + len < 256
  hl : 0 < len

/-- What a butterfly leaves. -/
structure BOut (s : State) (p : Addr) (G' : Poly) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → r ≠ .esi → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r
  esi : s'.gpr .esi = s.gpr .esi + 4
  edi : s'.gpr .edi = s.gpr .edi + 4
  ecx : s'.gpr .ecx = s.gpr .ecx - 1
  ne : eval .ne s' = some (!(s.gpr .ecx - 1 == 0))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [polyRegion p] s.mem s'.mem
  poly : PolyIs s'.mem p G'

theorem inRd {s : State} {a : Addr} (h : InRegions s.wr a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

theorem bfly_set (G : Poly) {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) :
    bfly G j len z = (G.set! (j + len) (G[j]! - z * G[j + len]!)).set! j (G[j]! + z * G[j + len]!) := by
  simp only [bfly]
  rw [getElem!_set!_ne _ (by omega) (by omega)]

theorem bflyInv_set (G : Poly) {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) :
    bflyInv G j len z = (G.set! j (G[j]! + G[j + len]!)).set! (j + len) (z * (G[j + len]! - G[j]!)) := by
  simp only [bflyInv]
  rw [getElem!_set!_ne _ (by omega) (by omega)]

theorem sub_val_eq (a t : Zq) : (a - t).val = (a.val + q - t.val) % q := by
  rw [val_sub, condSub_eq (by have := a.isLt; have := t.isLt; omega)]

theorem add_val_eq (a t : Zq) : (a + t).val = (a.val + t.val) % q := by
  rw [val_add, condSub_eq (by have := a.isLt; have := t.isLt; omega)]

theorem bfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Nat}
    (h : VG.Proof.MlKem.X86.BIn s p G j len zA z) : WP isa (.block bflyBody) s (VG.Proof.MlKem.X86.BOut s p (bfly G j len (ofNat z))) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := polyIs_coeffAt h.poly hj
  have hb := polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  have lz := h.z_lt
  rw [coeffAt_eq] at ha hb
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  have lz' : z < 3329 := q_eq ▸ h.z_lt
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 z).toNat = z := toNat_ofNat32 (by omega)
  have hbz : b * z < 2 ^ 32 := by rw [q_eq] at lz; have := Nat.mul_lt_mul_of_lt_of_lt lb lz; omega
  rw [bflyBody, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_movm ?_ (wp_movm ?_ (VG.Proof.MlKem.X86.wp_mul (wp_movr (VG.Proof.MlKem.X86.red_spec (r := .ebx) (by decide) (by decide) _ _ _
    (x := b * z) ?_ ?_ fun s₂ o₂ v₂ => ?_))))
  · rw [State.ea, at_]; exact h.ea_d ▸ VG.Proof.MlKem.X86.inRd h.in_d
  · simp only [State.ea, at_, State.setReg, show Reg.ebp ≠ Reg.eax by decide, ite_false, h.ea_z]
    exact h.in_z
  · simp only [reduceCtorEq, ↓reduceIte, State.setReg, VG.Proof.MlKem.X86.execMul_eax, State.ea,
      at_, h.ea_d, h.ea_z, hb, h.z_v]
    rw [hb', hz', toNat_ofNat32 hbz]
  · simp only [reduceCtorEq, ↓reduceIte, State.setReg, VG.Proof.MlKem.X86.execMul_eax, State.ea,
      at_, h.ea_d, h.ea_z, hb, h.z_v]
    rw [hb', hz', toNat_ofNat32 hbz]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]
    simp only [State.setReg, h3, ite_false]
    rw [VG.Proof.MlKem.X86.execMul_other _ _ h1 h2]
    simp only [h1, h2, ite_false]
  have m₁ : s₂.mem = s.mem := o₂.mem
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := m₁
  have rd₂ : s₂.rd = s.rd := o₂.rd
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 (b * z % q) := eq_ofNat_of_toNat v₂
  have hrw : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p (j + len)) V).readW (coeffAddr p j) 32 =
      s.mem.readW (coeffAddr p j) 32 := fun V => coeffAt_writeW_ne _ _ hj hjl (by omega) V
  have inI := h.in_i
  have inD := h.in_d
  have inI' := VG.Proof.MlKem.X86.inRd h.in_i
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, csub, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, at_, State.load32, State.store32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, esi₂, edi₂, ecx₂, m₂,
    rd₂, wr₂, bx₂, ea_i, ea_d, inI, inD, inI', hrw, ha, Option.some.injEq,
    exists_eq_left']
  have lt := Nat.mod_lt (b * z) (show q > 0 by rw [q_eq]; decide)
  rw [q_eq] at lt
  have e1 : (BitVec.ofNat 32 a + Q - BitVec.ofNat 32 (b * z % q)).toNat = a + q - b * z % q := by
    have hQ : (BitVec.ofNat 32 a + Q).toNat = a + 3329 := by
      rw [BitVec.toNat_add, toNat_ofNat32 (by omega), show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, toNat_ofNat32 (by rw [q_eq]; omega)]; rw [q_eq]; omega),
      hQ, toNat_ofNat32 (by rw [q_eq]; omega), q_eq]
  have e2 : (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * z % q)).toNat = a + b * z % q := by
    rw [BitVec.toNat_add, toNat_ofNat32 (by omega), toNat_ofNat32 (by rw [q_eq]; omega),
      Nat.mod_eq_of_lt (by rw [q_eq]; omega)]
  rw [csub_eq (BitVec.ofNat 32 a + Q - BitVec.ofNat 32 (b * z % q)) _ (by rw [e1, q_eq]; omega),
    csub_eq (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * z % q)) _ (by rw [e2, q_eq]; omega), e1, e2]
  have ht : (ofNat z * G[j + len]!).val = b * z % q := by
    rw [val_mul, ofNat_of_lt h.z_lt, eb, Nat.mul_comm]
  have hv1 : BitVec.ofNat 32 ((a + q - b * z % q) % q) = BitVec.ofNat 32 ((G[j]! - ofNat z * G[j + len]!).val) := by
    rw [VG.Proof.MlKem.X86.sub_val_eq, ht, ea]
  have hv2 : BitVec.ofNat 32 ((a + b * z % q) % q) = BitVec.ofNat 32 ((G[j]! + ofNat z * G[j + len]!).val) := by
    rw [VG.Proof.MlKem.X86.add_val_eq, ht, ea]
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h1, h2, h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)
  · rw [hv1, hv2, VG.Proof.MlKem.X86.bfly_set G hl hjl]
    exact polyIs_writeW (polyIs_writeW h.poly hjl _) hj _

theorem ibflyBody_eq : ibflyBody =
    (([.mov .ebx (.mem (at_ .edi 0)), .alu .add .ebx (.imm Q), .alu .sub .ebx (.mem (at_ .esi 0)),
      .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] : List Instr) ++ csub .eax .edx ++
      ([.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx,
        .mov .ebx (.reg .eax)] : List Instr)) ++
    (red .ebx ++ ([.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .ecx (.imm 1)] : List Instr)) := rfl

theorem ibfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Nat}
    (h : VG.Proof.MlKem.X86.BIn s p G j len zA z) : WP isa (.block ibflyBody) s (VG.Proof.MlKem.X86.BOut s p (bflyInv G j len (ofNat z))) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := polyIs_coeffAt h.poly hj
  have hb := polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  rw [coeffAt_eq] at ha hb
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  have lz' : z < 3329 := q_eq ▸ h.z_lt
  have ha' : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 z).toNat = z := toNat_ofNat32 (by omega)
  have hbz : (b + 3329 - a) * z < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show b + 3329 - a < 6658 by omega) lz'
    omega
  have hrw : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p j) V).readW (coeffAddr p (j + len)) 32 =
      s.mem.readW (coeffAddr p (j + len)) 32 := fun V => coeffAt_writeW_ne _ _ hjl hj (by omega) V
  have hrz : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p j) V).readW zA 32 = s.mem.readW zA 32 :=
    fun V => Mem.readW_writeW_sep h.z_sep (by decide)
  have inI := h.in_i
  have inD := h.in_d
  have inI' := VG.Proof.MlKem.X86.inRd h.in_i
  have inD' := VG.Proof.MlKem.X86.inRd h.in_d
  have inZ := h.in_z
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  have ea_z := h.ea_z
  have zv := h.z_v
  rw [VG.Proof.MlKem.X86.ibflyBody_eq, WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [csub, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc, State.ea, at_, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, ea_i, ea_d,
    ea_z, inI, inI', inD', inZ, ha, hb, hrz, zv, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hsub : (BitVec.ofNat 32 b + Q - BitVec.ofNat 32 a).toNat = b + 3329 - a := by
    have hQ : (BitVec.ofNat 32 b + Q).toNat = b + 3329 := by
      rw [BitVec.toNat_add, hb', show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, ha']; omega), hQ, ha']
  have hsum : (BitVec.ofNat 32 a + BitVec.ofNat 32 b).toNat = a + b := by
    rw [BitVec.toNat_add, ha', hb', Nat.mod_eq_of_lt (by omega)]
  refine VG.Proof.MlKem.X86.red_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := (b + 3329 - a) * z) ?_ ?_
    fun s₂ o₂ v₂ => ?_
  · simp only [ite_true, ite_false, reduceCtorEq]
    rw [hsub, hz', toNat_ofNat32 hbz]
  · simp only [ite_true, ite_false, reduceCtorEq]
    rw [hsub, hz', toNat_ofNat32 hbz]
  have m₂ := o₂.mem
  rw [csub_eq _ _ (by rw [hsum, q_eq]; omega), hsum] at m₂
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]
    simp only [h1, h2, h3, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have rd₂ : s₂.rd = s.rd := o₂.rd
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 ((b + 3329 - a) * z % q) := eq_ofNat_of_toNat v₂
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₂, edi₂, ecx₂, m₂, rd₂, wr₂, bx₂, ea_d, inD, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hv1 : BitVec.ofNat 32 ((a + b) % q) = BitVec.ofNat 32 ((G[j]! + G[j + len]!).val) := by
    rw [VG.Proof.MlKem.X86.add_val_eq, ea, eb]
  have hv2 : BitVec.ofNat 32 ((b + 3329 - a) * z % q) =
      BitVec.ofNat 32 ((ofNat z * (G[j + len]! - G[j]!)).val) := by
    rw [val_mul, VG.Proof.MlKem.X86.sub_val_eq, ofNat_of_lt h.z_lt, ea, eb, q_eq, Nat.mul_comm z, Nat.mul_mod,
      Nat.mod_eq_of_lt (a := z) lz']
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)
  · rw [hv1, hv2, VG.Proof.MlKem.X86.bflyInv_set G hl hjl]
    exact polyIs_writeW (polyIs_writeW h.poly hj _) hjl _

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Table`. -/
section

/-!
# ML-KEM on x86 (32-bit): writing a table of constants

`table T b` stores the 128 entries of `T` as words at `[b]`, through `edx`
(`table_spec`), one entry at a time (`tableN`), so that each step is a short
symbolic execution. The table is read like the first half of a polynomial
(`coeffAt`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- Entry `k` of the table. -/
def entry (T : List Nat) (b : Reg) (k : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ b (4 * k)) .edx]

/-- The first `n` entries. -/
def tableN (T : List Nat) (b : Reg) (n : Nat) : List Instr := (List.range n).flatMap (VG.Proof.MlKem.X86.entry T b)

theorem table_eq (T : List Nat) (b : Reg) : table T b = VG.Proof.MlKem.X86.tableN T b 128 := rfl

theorem tableN_succ (T : List Nat) (b : Reg) (n : Nat) :
    VG.Proof.MlKem.X86.tableN T b (n + 1) = VG.Proof.MlKem.X86.tableN T b n ++ VG.Proof.MlKem.X86.entry T b n := by
  simp only [VG.Proof.MlKem.X86.tableN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` entries of `T` at `p`, from `b` at `p`: only `edx`, the flags and the words at `p`
change. -/
theorem tableN_spec (T : List Nat) {b : Reg} (hb : b ≠ .edx) {p : Addr} :
    ∀ (n : Nat) (is : List Instr) (s : State) (P : State → Prop), n ≤ 128 →
      (∀ k < 128, s.ea (at_ b (4 * k)) = coeffAddr p k) → (∀ k < 128, InRegions s.wr (coeffAddr p k) 4) →
      (∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ k < n, coeffAt s'.mem p k = BitVec.ofNat 32 (T.getD k 0)) →
        (∀ k, n ≤ k → k < 256 → coeffAt s'.mem p k = coeffAt s.mem p k) → WP isa (.block is) s' P) →
      WP isa (.block (VG.Proof.MlKem.X86.tableN T b n ++ is)) s P
  | 0, is, s, P, _, _, _, k => k s ⟨fun _ _ => rfl, rfl, rfl⟩ (Frame.refl _ _) (fun _ h => absurd h (by omega))
      fun _ _ _ => rfl
  | n + 1, is, s, P, hn, hea, hin, k => by
    rw [VG.Proof.MlKem.X86.tableN_succ, List.append_assoc]
    refine VG.Proof.MlKem.X86.tableN_spec T hb n _ s P (by omega) hea hin fun s₁ o₁ f₁ c₁ d₁ => ?_
    have ea₁ : s₁.ea (at_ b (4 * n)) = coeffAddr p n := by
      rw [← hea n (by omega)]; simp only [State.ea, at_, o₁.gpr b (by simp [hb])]
    have hn' : n < Spec.MlKem.n := by rw [n_eq]; omega
    refine wp_cons (s' := s₁.setReg .edx (BitVec.ofNat 32 (T.getD n 0)))
      (by simp only [exec, readSrc, Option.map_some]) ?_
    have hin' : InRegions (s₁.setReg .edx (BitVec.ofNat 32 (T.getD n 0))).wr
        ((s₁.setReg .edx (BitVec.ofNat 32 (T.getD n 0))).ea (at_ b (4 * n))) 4 := by
      simp only [State.ea, at_, State.setReg, hb, ite_false]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁, o₁.wr]
      exact hin n (by omega)
    refine wp_store hin' ?_
    refine k _ ⟨fun r hr => ?_, o₁.rd, o₁.wr⟩ ?_ ?_ ?_
    · simp only [List.mem_singleton] at hr
      show (s₁.setReg .edx _).gpr r = s.gpr r
      simp only [State.setReg, hr, ite_false]
      exact o₁.gpr r (by simp [hr])
    · simp only [State.ea, at_, State.setReg, hb, ite_false]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn')
    · intro j hj
      simp only [State.ea, at_, State.setReg, hb, ite_false, ite_true]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlKem.n by rw [n_eq]; omega) hn']
      by_cases e : n = j
      · rw [ite_eq_left e, e]
      · rw [ite_eq_right e]; exact c₁ j (by omega)
    · intro j hj hj'
      simp only [State.ea, at_, State.setReg, hb, ite_false, ite_true]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlKem.n by rw [n_eq]; omega) hn', ite_eq_right (by omega),
        d₁ j (by omega) hj']

theorem table_spec (T : List Nat) {b : Reg} (hb : b ≠ .edx) {p : Addr} (is : List Instr) (s : State)
    (P : State → Prop) (hea : ∀ k < 128, s.ea (at_ b (4 * k)) = coeffAddr p k)
    (hin : ∀ k < 128, InRegions s.wr (coeffAddr p k) 4)
    (k : ∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
      (∀ k < 128, coeffAt s'.mem p k = BitVec.ofNat 32 (T.getD k 0)) → WP isa (.block is) s' P) :
    WP isa (.block (table T b ++ is)) s P := by
  rw [VG.Proof.MlKem.X86.table_eq]
  exact VG.Proof.MlKem.X86.tableN_spec T hb 128 is s P (Nat.le_refl _) hea hin fun s' o f c _ => k s' o f c

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.NttLoop`. -/
section

/-!
# ML-KEM on x86 (32-bit): the layers of the NTT and its inverse

A layer (`Impl.MlKem.X86.layerCode body dz len`) is a loop over its blocks,
each a loop of butterflies `body`; this file proves it once for any butterfly
that computes a function `op` of the polynomial (`Bfly`), with `ebp` moving up
(`dz = zUp`) or down (`zDown`) the zeta table, from its entry state `s₀`
(`vg_mlkem_ntt(f, scratch)` or `vg_mlkem_inv_ntt(f, scratch)`, after the setup
that stores the table in `scratch` and `f + 1024` in the argument slot of
`scratch`).

* `blockN op H len k start t`: the first `t` butterflies of a block;
  `layerN op kf P len c`: the first `c` blocks of a layer, block `c` with
  the zeta `kf len c` (as in `Ntt.lean`, of which these are `nttBlockN`,
  `nttLayerN` and their inverses).
* `MemOK s₀ G m`: memory holds `G` at `f`, the table, `f` and `f + 1024`
  in the argument slots, and differs from the entry only in `f`, `scratch`
  and the arguments.
-/

namespace VG.Proof.MlKem.X86.NttLoop

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev sP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (VG.Proof.MlKem.X86.NttLoop.fP s₀).setWidth 64
abbrev sA : Addr := (VG.Proof.MlKem.X86.NttLoop.sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀), polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), VG.Proof.MlKem.X86.NttLoop.aR s₀]
  f_s : (polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀))
  f_a : (polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀)).Disjoint (VG.Proof.MlKem.X86.NttLoop.aR s₀)
  s_a : (polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀)).Disjoint (VG.Proof.MlKem.X86.NttLoop.aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlKem.X86.NttLoop.aR s₀)
  stk_f : (VG.Proof.MlKem.X86.NttLoop.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀))
  stk_s : (VG.Proof.MlKem.X86.NttLoop.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀))
  stk_a : (VG.Proof.MlKem.X86.NttLoop.stkR s₀).Disjoint (VG.Proof.MlKem.X86.NttLoop.aR s₀)
  f_fit : (VG.Proof.MlKem.X86.NttLoop.fP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (VG.Proof.MlKem.X86.NttLoop.sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (VG.Proof.MlKem.X86.NttLoop.fA s₀)

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

theorem pub_esp {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.NttLoop.Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlKem.X86.NttLoop.Pre s₀)
include hp

theorem stk_eq : VG.Proof.MlKem.X86.NttLoop.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlKem.X86.NttLoop.stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem arg_in {i : Nat} (hi : i < 2) : (VG.Proof.MlKem.X86.NttLoop.aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

theorem in_f {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (VG.Proof.MlKem.X86.NttLoop.fA s₀) k) 4 :=
  ⟨polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀), by rw [hw, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩

theorem in_s {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (VG.Proof.MlKem.X86.NttLoop.sA s₀) k) 4 :=
  ⟨polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), by rw [hw, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩

theorem in_a {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 2) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.MlKem.X86.NttLoop.aR s₀, List.mem_append_right _ (by rw [hw, P0_wr, hp.wr]; simp), hp.arg_in hi⟩

/-- The push changes nothing of `f`, `scratch` or the arguments. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  exact hf

end Pre

/-! ## Memory -/

/-- Memory during the layers, holding `G` at `f`. -/
structure MemOK (s₀ : State) (G : Poly) (m : Mem) : Prop where
  frame : Frame [polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀), polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), VG.Proof.MlKem.X86.NttLoop.aR s₀] (P0 s₀).mem m
  tbl : ∀ k < 128, coeffAt m (VG.Proof.MlKem.X86.NttLoop.sA s₀) k = BitVec.ofNat 32 (zetas.getD k 0)
  arg0 : m.readW (argAddr s₀ 0) 32 = VG.Proof.MlKem.X86.NttLoop.fP s₀
  slot : m.readW (argAddr s₀ 1) 32 = VG.Proof.MlKem.X86.NttLoop.fP s₀ + 1024
  poly : PolyIs m (VG.Proof.MlKem.X86.NttLoop.fA s₀) G

/-- Writes to `f` keep the rest. -/
theorem MemOK.step {s₀ : State} (hp : VG.Proof.MlKem.X86.NttLoop.Pre s₀) {G G' : Poly} {m m' : Mem} (h : VG.Proof.MlKem.X86.NttLoop.MemOK s₀ G m)
    (hf : Frame [polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀)] m m') (hG : PolyIs m' (VG.Proof.MlKem.X86.NttLoop.fA s₀) G') : VG.Proof.MlKem.X86.NttLoop.MemOK s₀ G' m' where
  frame := h.frame.trans (hf.mono fun r hr => by simp at hr ⊢; exact .inl hr)
  tbl k hk := by
    rw [coeffAt_congr (m := m) (fun j hj => hf.bytes (R := polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀))
      (by simpa using hp.f_s.symm) (polyLen _) hj) (by rw [n_eq]; omega)]
    exact h.tbl k hk
  arg0 := by rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.arg0
  slot := by rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.slot
  poly := hG

/-! ## The butterflies of a block -/

/-- A butterfly code and the function of the polynomial it computes. -/
structure Bfly where
  body : List Instr
  op : Poly → Nat → Nat → Zq → Poly
  spec : ∀ {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Nat},
    VG.Proof.MlKem.X86.BIn s p G j len zA z → WP isa (.block body) s (VG.Proof.MlKem.X86.BOut s p (op G j len (ofNat z)))

/-- The first `t` butterflies of a block. -/
def blockN (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len k start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => op f j len (zeta k)) f

theorem blockN_succ (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len k start t : Nat) :
    VG.Proof.MlKem.X86.NttLoop.blockN op f len k start (t + 1) = op (VG.Proof.MlKem.X86.NttLoop.blockN op f len k start t) (start + t) len (zeta k) :=
  foldl_range'_succ _ _ _ _

/-- The first `c` blocks of a layer, block `c` with the zeta `kf len c`. -/
def layerN (op : Poly → Nat → Nat → Zq → Poly) (kf : Nat → Nat → Nat) (f : Poly) (len c : Nat) : Poly :=
  (List.range c).foldl (fun f c => VG.Proof.MlKem.X86.NttLoop.blockN op f len (kf len c) (2 * len * c) len) f

theorem layerN_succ (op : Poly → Nat → Nat → Zq → Poly) (kf : Nat → Nat → Nat) (f : Poly) (len c : Nat) :
    VG.Proof.MlKem.X86.NttLoop.layerN op kf f len (c + 1) = VG.Proof.MlKem.X86.NttLoop.blockN op (VG.Proof.MlKem.X86.NttLoop.layerN op kf f len c) len (kf len c) (2 * len * c) len :=
  foldl_range_succ _ _ _

/-- In a block: `t` butterflies done. -/
structure BL (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (H : Poly) (len k start t : Nat)
    (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem.X86.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * (start + t))
  edi : s.gpr .edi = VG.Proof.MlKem.X86.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * (start + len + t))
  ebp : s.gpr .ebp = VG.Proof.MlKem.X86.NttLoop.sP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (len - t)
  mem : VG.Proof.MlKem.X86.NttLoop.MemOK s₀ (VG.Proof.MlKem.X86.NttLoop.blockN op H len k start t) s.mem

theorem zetas_lt {k : Nat} (hk : k < 128) : zetas.getD k 0 < q := by
  rw [zetas_getD hk]; exact (zeta k).isLt

theorem bfly_step {s₀ : State} (hp : VG.Proof.MlKem.X86.NttLoop.Pre s₀) (b : VG.Proof.MlKem.X86.NttLoop.Bfly) {H : Poly} {len k start t : Nat}
    (hl : 0 < len) (hs : start + 2 * len ≤ 256) (hk : k < 128) (ht : t < len) {s : State}
    (h : VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op H len k start t s) :
    WP isa (.block b.body) s fun s' => VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op H len k start (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < len)) := by
  have ff := hp.f_fit
  have fs := hp.s_fit
  have bin : VG.Proof.MlKem.X86.BIn s (VG.Proof.MlKem.X86.NttLoop.fA s₀) (VG.Proof.MlKem.X86.NttLoop.blockN b.op H len k start t) (start + t) len (coeffAddr (VG.Proof.MlKem.X86.NttLoop.sA s₀) k)
      (zetas.getD k 0) := {
    ea_i := by rw [h.esi, ea_add (by omega), Nat.add_zero]
    ea_d := by rw [h.edi, ea_add (by omega), Nat.add_zero]; congr 2; omega
    ea_z := by rw [h.ebp, ea_add (by omega), Nat.add_zero]
    in_i := hp.in_f h.wr (by omega)
    in_d := hp.in_f h.wr (by omega)
    in_z := VG.Proof.MlKem.X86.inRd (hp.in_s h.wr (by omega))
    z_v := by rw [← coeffAt_eq, h.mem.tbl k hk]
    z_lt := VG.Proof.MlKem.X86.NttLoop.zetas_lt hk
    z_sep := hp.f_s.symm.sep (coeff_contains _ (by rw [n_eq]; omega)) (coeff_contains _ (by rw [n_eq]; omega))
    poly := h.mem.poly
    hj := by omega
    hl := hl }
  refine (b.spec bin).mono fun s' o => ⟨⟨?_, o.rd.trans h.rd, o.wr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esp]
  · rw [o.esi, h.esi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · rw [o.edi, h.edi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · rw [o.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ebp]
  · rw [o.ecx, h.ecx]; exact cnt_next ht
  · rw [VG.Proof.MlKem.X86.NttLoop.blockN_succ, zeta_eq hk]
    exact h.mem.step hp o.frame o.poly
  · rw [o.ne, h.ecx]
    exact (Option.map_some (f := (!·)) _).symm.trans (cnt_ne ht (by omega))

/-! ## The blocks of a layer -/

/-- In a layer: `c` blocks done. -/
structure KL (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (kf : Nat → Nat → Nat) (P : Poly)
    (len c : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem.X86.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  ebp : s.gpr .ebp = VG.Proof.MlKem.X86.NttLoop.sP s₀ + BitVec.ofNat 32 (4 * kf len c)
  mem : VG.Proof.MlKem.X86.NttLoop.MemOK s₀ (VG.Proof.MlKem.X86.NttLoop.layerN op kf P len c) s.mem

/-- Between layers. -/
structure LB (s₀ : State) (G : Poly) (z : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebp : s.gpr .ebp = VG.Proof.MlKem.X86.NttLoop.sP s₀ + BitVec.ofNat 32 (4 * z)
  mem : VG.Proof.MlKem.X86.NttLoop.MemOK s₀ G s.mem

variable (b : VG.Proof.MlKem.X86.NttLoop.Bfly) (kf : Nat → Nat → Nat) (P : State → Poly)

theorem blockInit_piece (len c : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block (blockInit len)) hc).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.KL s₀ b.op kf (P s₀) len c s)
      (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op (VG.Proof.MlKem.X86.NttLoop.layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) 0 s)
      (.block (blockInit len)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht
  apply WP.of_runBlock
  simp only [blockInit, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.map_some,
    Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], ?_, by simp [h.ebp], by simp, ?_⟩
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.esi]
    rw [add_ofNat_add]; congr 2; omega
  · rw [VG.Proof.MlKem.X86.NttLoop.blockN, List.range'_zero, List.foldl_nil]; exact h.mem

theorem bflyLoop_piece (len c : Nat) (hl : 0 < len) (hs : 2 * len * c + 2 * len ≤ 256)
    (hk : kf len c < 128) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block b.body) hc).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub
      (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op (VG.Proof.MlKem.X86.NttLoop.layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) 0 s)
      (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op (VG.Proof.MlKem.X86.NttLoop.layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) len s)
      (.loop (.block b.body) .ne) :=
  Piece.countLoop hl (fun t s₀ s => VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op (VG.Proof.MlKem.X86.NttLoop.layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) t s)
    [.esp, .esi, .edi, .ebp, .ecx]
    (fun t ht s₀ s hp h => VG.Proof.MlKem.X86.NttLoop.bfly_step hp b hl hs hk ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.NttLoop.pub_esp hq]
      · rw [h.esi, h'.esi, VG.Proof.MlKem.X86.NttLoop.fP, VG.Proof.MlKem.X86.NttLoop.fP, hq.2.1]
      · rw [h.edi, h'.edi, VG.Proof.MlKem.X86.NttLoop.fP, VG.Proof.MlKem.X86.NttLoop.fP, hq.2.1]
      · rw [h.ebp, h'.ebp, VG.Proof.MlKem.X86.NttLoop.sP, VG.Proof.MlKem.X86.NttLoop.sP, hq.2.2]
      · rw [h.ecx, h'.ecx]) ht

/-- `ebp` moves up (`zUp`) or down (`zDown`) to the next zeta. -/
def dzOf (up : Bool) : Instr := if up then zUp else zDown

theorem ptr_prev (x : BitVec 32) {a b : Nat} (h : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  rw [show x + BitVec.ofNat 32 a = x + BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [add_ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

/-- The loop over blocks goes on while blocks are left. -/
theorem blk_cond {len B c : Nat} (hB : len * B = 128) (hc : c < B) :
    (!decide (4 * (2 * len * c + len + len) = 1024)) = decide (c + 1 < B) := by
  have hl : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h | h
    · rw [h, Nat.zero_mul] at hB; exact absurd hB (by decide)
    · exact h
  have e : 4 * (2 * len * c + len + len) = 8 * (len * (c + 1)) := by
    rw [Nat.mul_succ, Nat.mul_assoc 2]; omega
  rw [e]
  by_cases h : c + 1 = B
  · rw [h, hB]; simp
  · have hlt : len * (c + 1) < len * B := Nat.mul_lt_mul_of_pos_left (by omega) hl
    rw [hB] at hlt
    simp only [show ¬ 8 * (len * (c + 1)) = 1024 by omega, decide_false, Bool.not_false,
      show c + 1 < B by omega, decide_true]

/-- The pointer compared with the end of `f`. -/
theorem end_cmp (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)

theorem blockEnd_piece (up : Bool) (len c B : Nat) (hB : len * B = 128) (hc : c < B)
    (hkf : kf len (c + 1) = if up then kf len c + 1 else kf len c - 1)
    (hk : up = false → 1 ≤ kf len c) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd (VG.Proof.MlKem.X86.NttLoop.dzOf up))) hh).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub
      (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.BL s₀ b.op (VG.Proof.MlKem.X86.NttLoop.layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) len s)
      (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.KL s₀ b.op kf (P s₀) len (c + 1) s ∧ eval .ne s = some (decide (c + 1 < B)))
      (.block (blockEnd (VG.Proof.MlKem.X86.NttLoop.dzOf up))) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have ff := hp.f_fit
    have hsl : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by
      rw [h.esp]; exact P0_argAddr s₀ 1
    have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := hp.in_a h.wr (by decide)
    have hlc : 2 * len * c + 2 * len ≤ 256 := by
      have : len * (c + 1) ≤ len * B := Nat.mul_le_mul_left _ hc
      rw [Nat.mul_succ] at this; rw [Nat.mul_assoc]; omega
    apply WP.of_runBlock
    cases up
    all_goals
      simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, blockEnd, VG.Proof.MlKem.X86.NttLoop.dzOf, zUp, zDown, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, Option.map_some, Option.bind_some, State.setReg, arithFlags,
        State.setFlags, State.ea, at_, State.load32, hsl, ins, h.mem.slot,
        Option.some.injEq, exists_eq_left']
      refine ⟨⟨by simp [h.esp], h.rd, h.wr, ?_, ?_, ?_⟩, ?_⟩
    · simp only [show Reg.esi ≠ Reg.ebp by decide, ite_false, ite_true, h.edi]
      congr 2; rw [Nat.mul_succ]; omega
    · simp only [ite_true, h.ebp, hkf, Bool.false_eq_true, ite_false]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlKem.X86.NttLoop.ptr_prev _ (by have := hk rfl; omega)]
      congr 2; have := hk rfl; omega
    · rw [VG.Proof.MlKem.X86.NttLoop.layerN_succ]; exact h.mem
    · simp only [eval, Option.map_some, h.edi]
      rw [VG.Proof.MlKem.X86.NttLoop.end_cmp _ (by omega), VG.Proof.MlKem.X86.NttLoop.blk_cond hB hc]
    · simp only [show Reg.esi ≠ Reg.ebp by decide, ite_false, ite_true, h.edi]
      congr 2; rw [Nat.mul_succ]; omega
    · simp only [ite_true, h.ebp, hkf, ite_true]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
    · rw [VG.Proof.MlKem.X86.NttLoop.layerN_succ]; exact h.mem
    · simp only [eval, Option.map_some, h.edi]
      rw [VG.Proof.MlKem.X86.NttLoop.end_cmp _ (by omega), VG.Proof.MlKem.X86.NttLoop.blk_cond hB hc]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, VG.Proof.MlKem.X86.NttLoop.pub_esp hq]

theorem layer_piece (up : Bool) (len B : Nat) (hB : len * B = 128) (hBp : 0 < B)
    (hkf : ∀ c < B, kf len (c + 1) = if up then kf len c + 1 else kf len c - 1)
    (hk : ∀ c < B, kf len c < 128) (hk1 : up = false → ∀ c < B, 1 ≤ kf len c)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block b.body) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd (VG.Proof.MlKem.X86.NttLoop.dzOf up))) h₄).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.LB s₀ (P s₀) (kf len 0) s)
      (fun s₀ s => VG.Proof.MlKem.X86.NttLoop.LB s₀ (VG.Proof.MlKem.X86.NttLoop.layerN b.op kf (P s₀) len B) (kf len B) s) (layerCode b.body (VG.Proof.MlKem.X86.NttLoop.dzOf up) len) := by
  have hl : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h | h
    · rw [h, Nat.zero_mul] at hB; exact absurd hB (by decide)
    · exact h
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.NttLoop.KL s₀ b.op kf (P s₀) len 0 s) ?_ ((Piece.loop
    (fun c s₀ s => VG.Proof.MlKem.X86.NttLoop.KL s₀ b.op kf (P s₀) len c s) hBp fun c hc =>
      Piece.seq (VG.Proof.MlKem.X86.NttLoop.blockInit_piece b kf P len c t₂) (Piece.seq (VG.Proof.MlKem.X86.NttLoop.bflyLoop_piece b kf P len c hl ?_ (hk c hc) t₃)
        (VG.Proof.MlKem.X86.NttLoop.blockEnd_piece b kf P up len c B hB hc (hkf c hc) (fun e => hk1 e c hc) t₄))).mono
    (fun _ _ _ h => h) fun _ _ _ h => ⟨h.esp, h.rd, h.wr, h.ebp, h.mem⟩)
  · refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₁
    · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
        rw [h.esp]; exact P0_argAddr s₀ 0
      have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
        State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨by simp [h.esp], h.rd, h.wr, by simp, by simp [h.ebp], ?_⟩
      rw [VG.Proof.MlKem.X86.NttLoop.layerN, List.range_zero, List.foldl_nil]; exact h.mem
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, VG.Proof.MlKem.X86.NttLoop.pub_esp hq]
  · have : len * (c + 1) ≤ len * B := Nat.mul_le_mul_left _ hc
    rw [Nat.mul_succ] at this; rw [Nat.mul_assoc]; omega

end VG.Proof.MlKem.X86.NttLoop

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Mul`. -/
section

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_multiply_ntts`

After storing the table of the `γᵢ` in `scratch` and `h + 1024` in the
argument slot of `scratch`, the loop computes pair `t` of `h`
(`multiplyNTTs_even`, `multiplyNTTs_odd`) with three reductions (`red_spec`)
and compares `h + 8(t + 1)` with that end.
-/

namespace VG.Proof.MlKem.X86.Mul

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

section
variable (s₀ : State)
abbrev hP : BitVec 32 := arg s₀ 0
abbrev fP : BitVec 32 := arg s₀ 1
abbrev gP : BitVec 32 := arg s₀ 2
abbrev sP : BitVec 32 := arg s₀ 3
abbrev hA : Addr := (VG.Proof.MlKem.X86.Mul.hP s₀).setWidth 64
abbrev fA : Addr := (VG.Proof.MlKem.X86.Mul.fP s₀).setWidth 64
abbrev gA : Addr := (VG.Proof.MlKem.X86.Mul.gP s₀).setWidth 64
abbrev sA : Addr := (VG.Proof.MlKem.X86.Mul.sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev Fp : Poly := polyAt s₀.mem (VG.Proof.MlKem.X86.Mul.fA s₀)
abbrev Gp : Poly := polyAt s₀.mem (VG.Proof.MlKem.X86.Mul.gA s₀)
/-- The value of coefficient `i` of `h`. -/
abbrev V (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (VG.Proof.MlKem.X86.Mul.Fp s₀) (VG.Proof.MlKem.X86.Mul.Gp s₀))[i]!).val
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀), polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀), polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀), VG.Proof.MlKem.X86.Mul.aR s₀]
  h_f : (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀))
  h_g : (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀))
  h_s : (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀))
  h_a : (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀)).Disjoint (VG.Proof.MlKem.X86.Mul.aR s₀)
  f_s : (polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀))
  f_a : (polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀)).Disjoint (VG.Proof.MlKem.X86.Mul.aR s₀)
  g_s : (polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀)).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀))
  g_a : (polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀)).Disjoint (VG.Proof.MlKem.X86.Mul.aR s₀)
  s_a : (polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀)).Disjoint (VG.Proof.MlKem.X86.Mul.aR s₀)
  ret_h : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀))
  ret_f : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlKem.X86.Mul.aR s₀)
  stk_h : (VG.Proof.MlKem.X86.Mul.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀))
  stk_f : (VG.Proof.MlKem.X86.Mul.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀))
  stk_g : (VG.Proof.MlKem.X86.Mul.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀))
  stk_s : (VG.Proof.MlKem.X86.Mul.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀))
  stk_a : (VG.Proof.MlKem.X86.Mul.stkR s₀).Disjoint (VG.Proof.MlKem.X86.Mul.aR s₀)
  h_fit : (VG.Proof.MlKem.X86.Mul.hP s₀).toNat + 1024 ≤ 2 ^ 32
  f_fit : (VG.Proof.MlKem.X86.Mul.fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (VG.Proof.MlKem.X86.Mul.gP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (VG.Proof.MlKem.X86.Mul.sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (VG.Proof.MlKem.X86.Mul.fA s₀)
  g_red : Reduced s₀.mem (VG.Proof.MlKem.X86.Mul.gA s₀)

theorem Pre.of {s₀ : State} (h : (mulContract X86.abi 16).pre s₀) : VG.Proof.MlKem.X86.Mul.Pre s₀ := by
  sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

theorem pub_esp {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.Mul.Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

/-- The regions the function writes. -/
abbrev W (s₀ : State) : List Region := [polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀), polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀), VG.Proof.MlKem.X86.Mul.aR s₀]

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlKem.X86.Mul.Pre s₀)
include hp

theorem stk_eq : VG.Proof.MlKem.X86.Mul.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlKem.X86.Mul.stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem arg_in {i : Nat} (hi : i < 4) : (VG.Proof.MlKem.X86.Mul.aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

theorem in_a {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.MlKem.X86.Mul.aR s₀, List.mem_append_right _ (by rw [hw, P0_wr, hp.wr]; simp), hp.arg_in hi⟩

theorem in_w {s : State} (hw : s.wr = (P0 s₀).wr) {r : Region} (hr : r ∈ VG.Proof.MlKem.X86.Mul.W s₀) {a : Addr} {n : Nat}
    (hc : r.Contains a n) : InRegions s.wr a n :=
  ⟨r, by rw [hw, P0_wr, hp.wr]; exact List.mem_cons_of_mem _ hr, hc⟩

theorem in_r {s : State} (hr' : s.rd = (P0 s₀).rd) {r : Region} (hr : r ∈ [polyRegion (VG.Proof.MlKem.X86.Mul.fA s₀), polyRegion (VG.Proof.MlKem.X86.Mul.gA s₀)])
    {a : Addr} {n : Nat} (hc : r.Contains a n) : InRegions (s.rd ++ s.wr) a n :=
  ⟨r, List.mem_append_left _ (by rw [hr', pushed_rd, hp.rd]; exact hr), hc⟩

/-- The push changes nothing but its frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  exact hf

/-- `f` and `g` keep their values. -/
theorem keep {m : Mem} (hf : Frame (VG.Proof.MlKem.X86.Mul.W s₀) (P0 s₀).mem m) {p : Addr}
    (hd : ∀ r ∈ frameR s₀ :: VG.Proof.MlKem.X86.Mul.W s₀, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAt m p i = coeffAt s₀.mem p i :=
  coeffAt_congr (fun j hj => bytes_frame ((hp.P0_keep.mono (by simp)).trans (hf.mono (by simp))) hd
    (by decide) j hj) (by rw [n_eq]; exact hi)

theorem f_keep {m : Mem} (hf : Frame (VG.Proof.MlKem.X86.Mul.W s₀) (P0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (VG.Proof.MlKem.X86.Mul.fA s₀) i = coeffAt s₀.mem (VG.Proof.MlKem.X86.Mul.fA s₀) i := by
  refine hp.keep hf (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [← hp.stk_eq]; exact hp.stk_f.symm
  · exact hp.h_f.symm
  · exact hp.f_s
  · exact hp.f_a

theorem g_keep {m : Mem} (hf : Frame (VG.Proof.MlKem.X86.Mul.W s₀) (P0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (VG.Proof.MlKem.X86.Mul.gA s₀) i = coeffAt s₀.mem (VG.Proof.MlKem.X86.Mul.gA s₀) i := by
  refine hp.keep hf (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [← hp.stk_eq]; exact hp.stk_g.symm
  · exact hp.h_g.symm
  · exact hp.g_s
  · exact hp.g_a

end Pre

/-- After `t` pairs. -/
structure MI (s₀ : State) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebx : s.gpr .ebx = VG.Proof.MlKem.X86.Mul.hP s₀ + BitVec.ofNat 32 (8 * t)
  esi : s.gpr .esi = VG.Proof.MlKem.X86.Mul.fP s₀ + BitVec.ofNat 32 (8 * t)
  edi : s.gpr .edi = VG.Proof.MlKem.X86.Mul.gP s₀ + BitVec.ofNat 32 (8 * t)
  ebp : s.gpr .ebp = VG.Proof.MlKem.X86.Mul.sP s₀ + BitVec.ofNat 32 (4 * t)
  frame : Frame (VG.Proof.MlKem.X86.Mul.W s₀) (P0 s₀).mem s.mem
  tbl : ∀ k < 128, coeffAt s.mem (VG.Proof.MlKem.X86.Mul.sA s₀) k = BitVec.ofNat 32 (gammas.getD k 0)
  slot : s.mem.readW (argAddr s₀ 3) 32 = VG.Proof.MlKem.X86.Mul.hP s₀ + 1024
  out : ∀ i < 2 * t, coeffAt s.mem (VG.Proof.MlKem.X86.Mul.hA s₀) i = VG.Proof.MlKem.X86.Mul.V s₀ i

theorem mul_even (a b c d γ : Zq) :
    (a * b + c * d * γ).val = (a.val * b.val + (c.val * d.val % q) * γ.val) % q := by
  rw [val_add', val_mul, val_mul, val_mul]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

theorem gamma_val {t : Nat} (ht : t < 128) : (gamma t).val = gammas.getD t 0 := (gammas_getD ht).symm

theorem mul_odd (a b c d : Zq) : (a * d + c * b).val = (a.val * d.val + c.val * b.val) % q := by
  rw [val_add', val_mul, val_mul, ← Nat.add_mod]

theorem mul_step {s₀ : State} (hp : VG.Proof.MlKem.X86.Mul.Pre s₀) {t : Nat} (ht : t < 128) {s : State} (h : VG.Proof.MlKem.X86.Mul.MI s₀ t s) :
    WP isa (.block mulBody) s fun s' => VG.Proof.MlKem.X86.Mul.MI s₀ (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 128)) := by
  have hf := hp.f_fit
  have hg := hp.g_fit
  have hh := hp.h_fit
  have hs := hp.s_fit
  have i0 : 2 * t < n := by rw [n_eq]; omega
  have i1 : 2 * t + 1 < n := by rw [n_eq]; omega
  have it : t < n := by rw [n_eq]; omega
  -- The addresses.
  have ea_f0 : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.fA s₀) (2 * t) := by
    rw [h.esi, ea_add (by omega)]; congr 2; omega
  have ea_f1 : (s.gpr .esi + BitVec.ofNat 32 4).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.fA s₀) (2 * t + 1) := by
    rw [h.esi, ea_add (by omega)]; congr 2; omega
  have ea_g0 : (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.gA s₀) (2 * t) := by
    rw [h.edi, ea_add (by omega)]; congr 2; omega
  have ea_g1 : (s.gpr .edi + BitVec.ofNat 32 4).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.gA s₀) (2 * t + 1) := by
    rw [h.edi, ea_add (by omega)]; congr 2; omega
  have ea_z : (s.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.sA s₀) t := by
    rw [h.ebp, ea_add (by omega), Nat.add_zero]
  have ea_h0 : (s.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t) := by
    rw [h.ebx, ea_add (by omega)]; congr 2; omega
  have ea_h1 : (s.gpr .ebx + BitVec.ofNat 32 4).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t + 1) := by
    rw [h.ebx, ea_add (by omega)]; congr 2; omega
  have ea_sl : (s.gpr .esp + BitVec.ofNat 32 32).setWidth 64 = argAddr s₀ 3 := by
    rw [h.esp]; exact P0_argAddr s₀ 3
  -- The permissions.
  have in_f0 := hp.in_r h.rd (List.mem_cons_self ..) (coeff_contains (VG.Proof.MlKem.X86.Mul.fA s₀) i0)
  have in_f1 := hp.in_r h.rd (List.mem_cons_self ..) (coeff_contains (VG.Proof.MlKem.X86.Mul.fA s₀) i1)
  have in_g0 := hp.in_r h.rd (by simp) (coeff_contains (VG.Proof.MlKem.X86.Mul.gA s₀) i0)
  have in_g1 := hp.in_r h.rd (by simp) (coeff_contains (VG.Proof.MlKem.X86.Mul.gA s₀) i1)
  have in_z : InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlKem.X86.Mul.sA s₀) t) 4 :=
    VG.Proof.MlKem.X86.inRd (hp.in_w h.wr (by simp) (coeff_contains (VG.Proof.MlKem.X86.Mul.sA s₀) it))
  have in_h0 : InRegions s.wr (coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t)) 4 := hp.in_w h.wr (by simp) (coeff_contains _ i0)
  have in_h1 : InRegions s.wr (coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t + 1)) 4 := hp.in_w h.wr (by simp) (coeff_contains _ i1)
  have in_sl := hp.in_a h.wr (i := 3) (by decide)
  -- The values.
  have vf0 := hp.f_keep h.frame (i := 2 * t) (by omega)
  have vf1 := hp.f_keep h.frame (i := 2 * t + 1) (by omega)
  have vg0 := hp.g_keep h.frame (i := 2 * t) (by omega)
  have vg1 := hp.g_keep h.frame (i := 2 * t + 1) (by omega)
  have vz := h.tbl t ht
  rw [coeffAt_eq] at vf0 vf1 vg0 vg1 vz
  have lf0 := hp.f_red (2 * t) i0
  have lf1 := hp.f_red (2 * t + 1) i1
  have lg0 := hp.g_red (2 * t) i0
  have lg1 := hp.g_red (2 * t + 1) i1
  have lz : gammas.getD t 0 < q := by rw [gammas_getD ht]; exact (gamma t).isLt
  have pf0 := polyAt_val hp.f_red i0
  have pf1 := polyAt_val hp.f_red i1
  have pg0 := polyAt_val hp.g_red i0
  have pg1 := polyAt_val hp.g_red i1
  generalize coeffAt s₀.mem (VG.Proof.MlKem.X86.Mul.fA s₀) (2 * t) = F0 at vf0 lf0 pf0
  generalize coeffAt s₀.mem (VG.Proof.MlKem.X86.Mul.fA s₀) (2 * t + 1) = F1 at vf1 lf1 pf1
  generalize coeffAt s₀.mem (VG.Proof.MlKem.X86.Mul.gA s₀) (2 * t) = G0 at vg0 lg0 pg0
  generalize coeffAt s₀.mem (VG.Proof.MlKem.X86.Mul.gA s₀) (2 * t + 1) = G1 at vg1 lg1 pg1
  rw [q_eq] at lf0 lf1 lg0 lg1 lz
  have p11 : F1.toNat * G1.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf1 lg1; omega
  rw [mulBody, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execMul,
    readSrc, State.ea, at_, State.load32, State.setReg, State.setFlags, Option.map_some, ea_f1, ea_g1,
    in_f1, in_g1, vf1, vg1, Option.some.injEq, exists_eq_left']
  refine VG.Proof.MlKem.X86.red_spec (r := .ecx) (by decide) (by decide) _ _ _ (x := F1.toNat * G1.toNat)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact toNat_ofNat32 p11)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact toNat_ofNat32 p11) fun s₁ o₁ v₁ => ?_
  have g₁ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₁.gpr r (by simp [h1, h2, h3])]; simp [h1, h2, h3]
  have esi₁ := g₁ .esi (by decide) (by decide) (by decide)
  have edi₁ := g₁ .edi (by decide) (by decide) (by decide)
  have ebp₁ := g₁ .ebp (by decide) (by decide) (by decide)
  have m₁ : s₁.mem = s.mem := o₁.mem
  have rd₁ : s₁.rd = s.rd := o₁.rd
  have wr₁ : s₁.wr = s.wr := o₁.wr
  have cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 (F1.toNat * G1.toNat % q) := eq_ofNat_of_toNat v₁
  have lr₁ := Nat.mod_lt (F1.toNat * G1.toNat) (show q > 0 by rw [q_eq]; decide)
  rw [q_eq] at lr₁
  have hzv : (BitVec.ofNat 32 (gammas.getD t 0)).toNat = gammas.getD t 0 := toNat_ofNat32 (by omega)
  have x2 : F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lr₁ lz
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg0
    rw [q_eq]; omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul,
    readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, esi₁, edi₁, ebp₁, cx₁, m₁, rd₁, wr₁, ea_z, ea_f0, ea_g0, in_z, in_f0, in_g0, vz, vf0,
    vg0, Option.some.injEq, exists_eq_left']
  have p00 : F0.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg0; omega
  have ev2 : (BitVec.ofNat 32 ((BitVec.ofNat 32 (F1.toNat * G1.toNat % q)).toNat *
      (BitVec.ofNat 32 (gammas.getD t 0)).toNat) + BitVec.ofNat 32 (F0.toNat * G0.toNat)).toNat =
      F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat := by
    rw [toNat_ofNat32 (n := F1.toNat * G1.toNat % q) (by rw [q_eq]; omega), hzv, BitVec.toNat_add,
      toNat_ofNat32 (by omega), toNat_ofNat32 p00, Nat.mod_eq_of_lt x2]
  refine VG.Proof.MlKem.X86.red_spec (r := .ecx) (by decide) (by decide) _ _ _
    (x := F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev2)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev2) fun s₂ o₂ v₂ => ?_
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]; simp [h1, h2, h3, g₁]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ebx₂ := g₂ .ebx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := o₂.mem
  have rd₂ : s₂.rd = s.rd := o₂.rd
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have cx₂ : s₂.gpr .ecx = BitVec.ofNat 32 ((F1.toNat * G1.toNat % q * gammas.getD t 0 +
      F0.toNat * G0.toNat) % q) := eq_ofNat_of_toNat v₂
  have sep : ∀ {p : Addr} {j : Nat}, (polyRegion p).Disjoint (polyRegion (VG.Proof.MlKem.X86.Mul.hA s₀)) → j < n →
      ∀ V : BitVec 32, (s.mem.writeW (coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t)) V).readW (coeffAddr p j) 32 =
        s.mem.readW (coeffAddr p j) 32 := fun hd hj V =>
    Mem.readW_writeW_sep (hd.sep (coeff_contains _ hj) (coeff_contains _ i0)) (by decide)
  have wf0 := sep hp.h_f.symm i0
  have wf1 := sep hp.h_f.symm i1
  have wg0 := sep hp.h_g.symm i0
  have wg1 := sep hp.h_g.symm i1
  have p01 : F0.toNat * G1.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg1; omega
  have p10 : F1.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf1 lg0; omega
  have x3 : F0.toNat * G1.toNat + F1.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg1
    have := Nat.mul_lt_mul_of_lt_of_lt lf1 lg0
    omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul,
    readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, esi₂, edi₂, ebx₂, cx₂, m₂, rd₂, wr₂, ea_h0, ea_f0, ea_g0, ea_f1,
    ea_g1, in_h0, in_f0, in_g0, in_f1, in_g1, wf0, wf1, wg0, wg1, vf0, vg0, vf1, vg1,
    Option.some.injEq, exists_eq_left']
  have ev3 : (BitVec.ofNat 32 (F0.toNat * G1.toNat) + BitVec.ofNat 32 (F1.toNat * G0.toNat)).toNat =
      F0.toNat * G1.toNat + F1.toNat * G0.toNat := by
    rw [BitVec.toNat_add, toNat_ofNat32 p01, toNat_ofNat32 p10, Nat.mod_eq_of_lt x3]
  refine VG.Proof.MlKem.X86.red_spec (r := .ecx) (by decide) (by decide) _ _ _ (x := F0.toNat * G1.toNat + F1.toNat * G0.toNat)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev3)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev3) fun s₃ o₃ v₃ => ?_
  have g₃ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₃.gpr r (by simp [h1, h2, h3])]; simp [h1, h2, h3, g₂]
  have esi₃ := g₃ .esi (by decide) (by decide) (by decide)
  have edi₃ := g₃ .edi (by decide) (by decide) (by decide)
  have ebx₃ := g₃ .ebx (by decide) (by decide) (by decide)
  have ebp₃ := g₃ .ebp (by decide) (by decide) (by decide)
  have esp₃ := g₃ .esp (by decide) (by decide) (by decide)
  have m₃ := o₃.mem
  have rd₃ : s₃.rd = s.rd := o₃.rd
  have wr₃ : s₃.wr = s.wr := o₃.wr
  have cx₃ : s₃.gpr .ecx = BitVec.ofNat 32 ((F0.toNat * G1.toNat + F1.toNat * G0.toNat) % q) :=
    eq_ofNat_of_toNat v₃
  generalize eH0 : BitVec.ofNat 32 ((F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat) % q) = H0
    at m₃
  have sl₂ : ∀ V₀ V₁ : BitVec 32, ((s.mem.writeW (coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t)) V₀).writeW
      (coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) (2 * t + 1)) V₁).readW (argAddr s₀ 3) 32 = VG.Proof.MlKem.X86.Mul.hP s₀ + 1024 := fun V₀ V₁ => by
    rw [Mem.readW_writeW_sep (hp.h_a.symm.sep (hp.arg_in (by decide)) (coeff_contains _ i1)) (by decide),
      Mem.readW_writeW_sep (hp.h_a.symm.sep (hp.arg_in (by decide)) (coeff_contains _ i0)) (by decide),
      h.slot]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, esi₃, edi₃, ebx₃, ebp₃, esp₃, cx₃, m₃, rd₃, wr₃, ea_h1, ea_sl, in_h1, in_sl, sl₂,
    Option.some.injEq, exists_eq_left']
  have v0 : H0 = VG.Proof.MlKem.X86.Mul.V s₀ (2 * t) := by
    rw [← eH0, VG.Proof.MlKem.X86.Mul.V, multiplyNTTs_even _ _ ht, VG.Proof.MlKem.X86.Mul.mul_even, pf0, pg0, pf1, pg1, VG.Proof.MlKem.X86.Mul.gamma_val ht, Nat.add_comm]
  have v1 : BitVec.ofNat 32 ((F0.toNat * G1.toNat + F1.toNat * G0.toNat) % q) = VG.Proof.MlKem.X86.Mul.V s₀ (2 * t + 1) := by
    rw [VG.Proof.MlKem.X86.Mul.V, multiplyNTTs_odd _ _ ht, VG.Proof.MlKem.X86.Mul.mul_odd, pf0, pg0, pf1, pg1]
  have hsep : ∀ {k : Nat}, k < 128 → ∀ j, j < n → Mem.Sep (coeffAddr (VG.Proof.MlKem.X86.Mul.sA s₀) k) 4 (coeffAddr (VG.Proof.MlKem.X86.Mul.hA s₀) j) 4 :=
    fun hk j hj => hp.h_s.symm.sep (coeff_contains _ (by rw [n_eq]; omega)) (coeff_contains _ hj)
  refine ⟨⟨by simp [esp₃, h.esp], h.rd, h.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [ite_true, show Reg.ebx ≠ Reg.ebp by decide, show Reg.ebx ≠ Reg.edi by decide,
      show Reg.ebx ≠ Reg.esi by decide, ite_false, h.ebx]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, show Reg.esi ≠ Reg.ebp by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, h.esi]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, show Reg.edi ≠ Reg.ebp by decide, ite_false, h.edi]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · exact (h.frame.writeW (by simp) _ (coeff_contains _ i0)).writeW (by simp) _ (coeff_contains _ i1)
  · intro k hk
    rw [coeffAt_writeW_sep _ _ _ (hsep hk _ i1), coeffAt_writeW_sep _ _ _ (hsep hk _ i0)]
    exact h.tbl k hk
  · exact sl₂ _ _
  · intro i hi
    rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) i1,
      coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) i0]
    by_cases e1 : 2 * t + 1 = i
    · rw [ite_eq_left e1, ← e1, v1]
    rw [ite_eq_right e1]
    by_cases e0 : 2 * t = i
    · rw [ite_eq_left e0, ← e0, v0]
    rw [ite_eq_right e0]
    exact h.out i (by omega)
  · simp only [eval, Option.map_some, h.ebx]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add, NttLoop.end_cmp _ (by omega)]
    by_cases e : t + 1 = 128
    · simp [e, show 8 * t = 1016 by omega]
    · simp only [show ¬ 8 * t + 8 = 1024 by omega, decide_false, Bool.not_false]
      simp only [Option.some.injEq]; exact (decide_eq_true (by omega)).symm

/-! ## The function -/

theorem arg_sep {s₀ : State} (hp : VG.Proof.MlKem.X86.Mul.Pre s₀) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) :
    Mem.Sep (argAddr s₀ i) 4 (argAddr s₀ j) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  have : i < j ∨ j < i := by omega
  bv_omega

/-- After `mulLd`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = VG.Proof.MlKem.X86.Mul.sP s₀

theorem ld_piece : Piece VG.Proof.MlKem.X86.Mul.Pre VG.Proof.MlKem.X86.Mul.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem.X86.Mul.S1 (.block mulLd) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₃ := P0_argAddr s₀ 3
    have i₃ := P0_argIn (s₀ := s₀) (n := 4) (i := 3) (by omega) fit (by simp [hp.wr])
    have v₃ := P0_arg hp.sp (n := 4) (i := 3) (by omega) fit (by simpa [← hp.stk_eq] using hp.stk_a)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
    apply WP.of_runBlock
    simp only [mulLd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₃, i₃, v₃, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', VG.Proof.MlKem.X86.Mul.pub_esp hq]

theorem setup_piece : Piece VG.Proof.MlKem.X86.Mul.Pre VG.Proof.MlKem.X86.Mul.Pub VG.Proof.MlKem.X86.Mul.S1 (VG.Proof.MlKem.X86.Mul.MI · 0) (.block mulSetup) := by
  refine Piece.taint [.esp, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have fs := hp.s_fit
    have fit := hp.sp'
    rw [mulSetup]
    refine VG.Proof.MlKem.X86.table_spec gammaTable (b := .eax) (by decide) (p := VG.Proof.MlKem.X86.Mul.sA s₀) _ s _
      (fun k hk => by
        show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
        rw [h.eax, ea_off (by omega)])
      (fun k hk => hp.in_w h.wr (by simp) (coeff_contains _ (by rw [n_eq]; omega))) fun s₁ o₁ f₁ c₁ => ?_
    have esp₁ : s₁.gpr .esp = (P0 s₀).gpr .esp := by rw [o₁.gpr .esp (by decide), h.esp]
    have eax₁ : s₁.gpr .eax = VG.Proof.MlKem.X86.Mul.sP s₀ := by rw [o₁.gpr .eax (by decide), h.eax]
    have wr₁ : s₁.wr = (P0 s₀).wr := o₁.wr.trans h.wr
    have rd₁ : s₁.rd = (P0 s₀).rd := o₁.rd.trans h.rd
    have ad : ∀ i, (s₁.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := fun i => by
      rw [esp₁]; exact P0_argAddr s₀ i
    have a20 := ad 0
    have a24 := ad 1
    have a28 := ad 2
    have a32 := ad 3
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a20 a24 a28 a32
    have ins : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (argAddr s₀ i) 4 := fun i hi => hp.in_a wr₁ hi
    have in0 := ins 0 (by decide)
    have in1 := ins 1 (by decide)
    have in2 := ins 2 (by decide)
    have in3 : InRegions s₁.wr (argAddr s₀ 3) 4 := hp.in_w wr₁ (by simp) (hp.arg_in (by decide))
    have hsa : ∀ i < 4, ∀ r ∈ [polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀)], (⟨argAddr s₀ i, 4⟩ : Region).Disjoint r := by
      intro i hi r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.s_a.symm.sub_left (sub_of_contains (hp.arg_in hi))
    have va : ∀ i < 4, s₁.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
      rw [f₁.readW (Region.contains_self _ _) (hsa i hi) (by decide), h.mem]
      exact P0_arg hp.sp (n := 4) (i := i) hi fit (by simpa [← hp.stk_eq] using hp.stk_a)
    have v0 := va 0 (by decide)
    have v1 := va 1 (by decide)
    have v2 := va 2 (by decide)
    have w1 : ∀ V : BitVec 32, (s₁.mem.writeW (argAddr s₀ 3) V).readW (argAddr s₀ 1) 32 = arg s₀ 1 :=
      fun V => by rw [Mem.readW_writeW_sep (VG.Proof.MlKem.X86.Mul.arg_sep hp (by decide) (by decide) (by decide)) (by decide), v1]
    have w2 : ∀ V : BitVec 32, (s₁.mem.writeW (argAddr s₀ 3) V).readW (argAddr s₀ 2) 32 = arg s₀ 2 :=
      fun V => by rw [Mem.readW_writeW_sep (VG.Proof.MlKem.X86.Mul.arg_sep hp (by decide) (by decide) (by decide)) (by decide), v2]
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.ea, at_, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a20, a24, a28, a32, in0, in1, in2, in3, v0, w1, w2, ite_true,
      ite_false, Option.some.injEq, exists_eq_left']
    have hs1 : Frame [polyRegion (VG.Proof.MlKem.X86.Mul.sA s₀)] (P0 s₀).mem s₁.mem := h.mem ▸ f₁
    refine ⟨by simp [esp₁], rd₁, wr₁, by simp, by simp, by simp, by simp [eax₁], ?_, ?_, ?_,
      fun i hi => absurd hi (by omega)⟩
    · exact (hs1.mono (by simp)).writeW (by simp) _ (hp.arg_in (by decide))
    · intro k hk
      rw [coeffAt_writeW_sep _ _ _ (hp.s_a.sep (coeff_contains _ (by rw [n_eq]; omega)) (hp.arg_in (by decide))),
        c₁ k hk]
      rfl
    · exact Mem.readW_writeW_self32 _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.Mul.pub_esp hq]
    · rw [h.eax, h'.eax, VG.Proof.MlKem.X86.Mul.sP, VG.Proof.MlKem.X86.Mul.sP, hq.2.2.2.2]

theorem loop_piece : Piece VG.Proof.MlKem.X86.Mul.Pre VG.Proof.MlKem.X86.Mul.Pub (VG.Proof.MlKem.X86.Mul.MI · 0) (VG.Proof.MlKem.X86.Mul.MI · 128) (.loop (.block mulBody) .ne) :=
  Piece.countLoop (by decide) (fun t s₀ s => VG.Proof.MlKem.X86.Mul.MI s₀ t s) [.esp, .ebx, .esi, .edi, .ebp]
    (fun t ht s₀ s hp h => VG.Proof.MlKem.X86.Mul.mul_step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.Mul.pub_esp hq]
      · rw [h.ebx, h'.ebx, VG.Proof.MlKem.X86.Mul.hP, VG.Proof.MlKem.X86.Mul.hP, hq.2.1]
      · rw [h.esi, h'.esi, VG.Proof.MlKem.X86.Mul.fP, VG.Proof.MlKem.X86.Mul.fP, hq.2.2.1]
      · rw [h.edi, h'.edi, VG.Proof.MlKem.X86.Mul.gP, VG.Proof.MlKem.X86.Mul.gP, hq.2.2.2.1]
      · rw [h.ebp, h'.ebp, VG.Proof.MlKem.X86.Mul.sP, VG.Proof.MlKem.X86.Mul.sP, hq.2.2.2.2]) (by taint_decide)

theorem hW {s₀ : State} (hp : VG.Proof.MlKem.X86.Mul.Pre s₀) : ∀ r ∈ VG.Proof.MlKem.X86.Mul.W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_h, hp.ret_h⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_s, hp.ret_s⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_a, hp.ret_a⟩

theorem piece : Piece VG.Proof.MlKem.X86.Mul.Pre VG.Proof.MlKem.X86.Mul.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.Mul.MI s₀ 128) s₀ s')
    Impl.MlKem.X86.multiplyNTTs :=
  Piece.leaf VG.Proof.MlKem.X86.Mul.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => VG.Proof.MlKem.X86.Mul.hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq VG.Proof.MlKem.X86.Mul.ld_piece (Piece.seq VG.Proof.MlKem.X86.Mul.setup_piece VG.Proof.MlKem.X86.Mul.loop_piece)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `0x400`, `0x800` and `0xc00` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 4 else if a = 0x500d then 8 else if a = 0x5011 then 0xc else 0

theorem verified : Verified X86.target Impl.MlKem.X86.multiplyNTTs (mulContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.out i (by rw [n_eq] at hi; omega)
  · let st := satState VG.Proof.MlKem.X86.Mul.satMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0xc00, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have a3 : arg st 3 = 0xc00 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, by decide, by decide, by decide, by decide, reduced_below (fun a ha => ?_) 0x400 (by decide),
      reduced_below (fun a ha => ?_) 0x800 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show VG.Proof.MlKem.X86.Mul.satMem a = 0
         simp only [VG.Proof.MlKem.X86.Mul.satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])

end VG.Proof.MlKem.X86.Mul

end
