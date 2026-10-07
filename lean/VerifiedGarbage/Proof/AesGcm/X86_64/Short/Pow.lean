import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Field48
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
import VerifiedGarbage.Proof.Gcm.Powers

/-!
# AES-GCM's short path on x86-64: the powers of the hash subkey

Untrusted: everything here is checked by Lean, and computes in the field
(`Proof/Gcm/Poly.lean`). `powers` stores the table of powers that `ghash`
reads (`TabF`: group `j`, lane `l` is `Tₖ` with `x · Tₖ = Hᵏ`,
`k = 4 j + 4 - l`, which is `TabOk`, `tabOk_of_F`): `H'`–`H'⁴` in SSE
(`vg_ghash_pclmul`'s `hInv` and `pows`, `powSse_ok`), as group 0
(`pow4_ok`), then each further group from one below it times a power
(`StitchZ.powLoad_ok`, `powMore_ok`), as far as `m'` (in `rax`) needs. The
registers the first block leaves: `powHead_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod Only const_ok ldrev_ok hInv_ok pows_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The table at `T` holds `n` groups of powers of `H`, in the field: lane
`l` of group `j` is `Tₖ` with `x · Tₖ = Hᵏ`, `k = 4 j + 4 - l`. -/
def TabF (m : Mem) (T : Addr) (H : Block) (n : Nat) : Prop :=
  ∀ j < n, ∀ l < 4, x * φ (m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128) = φ H ^ (4 * j + 4 - l)

theorem x_φ_hInvF_hpow (H : Block) (k : Nat) :
    x * φ (VG.Proof.Gcm.X86_64.StitchZP.hInvF (Spec.Gcm.hpow H k)) = φ H ^ k := by
  rw [VG.Proof.Gcm.X86_64.StitchZP.hInvF, VG.Proof.Gcm.X86_64.Pclmul.x_φ_hInv, φ_hpow]

/-- `x` has an inverse. -/
theorem x_inv : ∃ y, x * y = 1 := ⟨_, by rw [VG.Proof.Gcm.X86_64.Pclmul.x_φ_hInv, φ_one]⟩

theorem tabOk_of_F {m : Mem} {T : Addr} {H : Block} {n : Nat} (h : TabF m T H n) : TabOk m T H n :=
  fun j hj l hl => φ_inj (by
    obtain ⟨y, hy⟩ := x_inv
    have e := (h j hj l hl).trans (x_φ_hInvF_hpow H (4 * j + 4 - l)).symm
    calc _ = y * (x * φ (m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128)) := by
          rw [← mul_assoc, mul_comm y x, hy, one_mul]
      _ = _ := by rw [e, ← mul_assoc, mul_comm y x, hy, one_mul])

theorem F_of_tabOk {m : Mem} {T : Addr} {H : Block} {n : Nat} (h : TabOk m T H n) : TabF m T H n :=
  fun j hj l hl => by rw [h j hj l hl, x_φ_hInvF_hpow]

/-- `H'`–`H'⁴` in `xmm3`–`xmm6`, from the hash subkey at `r13 + 240`, and the
mask and the reduction constant in `xmm0` and `xmm1`. -/
theorem powSse_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int)) 16) :
    WP isa (.block powSse) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧
      x * φ (t.xmm .xmm3) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ∧
      x * φ (t.xmm .xmm4) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 2 ∧
      x * φ (t.xmm .xmm5) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 3 ∧
      x * φ (t.xmm .xmm6) = φ (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ 4 ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  simp only [powSse, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r13 240 s₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have x1 : s₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  refine WP.mono (pows_ok (H := blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) s₄ x1
    (by rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide)]))
    fun t ⟨H2, H3, H4, o⟩ => ?_
  have O := o₁₂.trans (o₃.trans (o₄.trans o))
  refine ⟨by rw [o.xmm _ (by decide), o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁,
    VG.Proof.Gcm.X86_64.Pclmul.rev_eq],
    by rw [o.xmm _ (by decide), x1], by rw [o.xmm _ (by decide), t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide)],
    H2, H3, H4, O.gpr, O.mem, O.rd, O.wr⟩

/-- The register of `H'⁴⁻ˡ`, lane `l` of group 0. -/
def pr4 : Nat → XReg
  | 0 => .xmm6 | 1 => .xmm5 | 2 => .xmm4 | _ => .xmm3

/-- `H'⁴`, `H'³`, `H'²`, `H'` into the lanes of `zmm8`. -/
theorem pow4a_ok (s : State) :
    WP isa (.block [.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
        .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44)]) s fun t =>
      (∀ l < 4, t.zlane .xmm8 l = s.xmm (pr4 l)) ∧ ZFrame [.xmm8, .xmm9] s t := by
  refine WP.mono (WP.zframe (rs := [.xmm8, .xmm9]) (by decide)
    (Q := fun t => ∀ l < 4, t.zlane .xmm8 l = s.xmm (pr4 l)) ?_) fun t h => h
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [VOp.exec]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [zlane_vshufi32x4, VG.Proof.Gcm.X86_64.StitchZ.shuf44_0, VG.Proof.Gcm.X86_64.StitchZ.shuf44_1,
    VG.Proof.Gcm.X86_64.StitchZ.shuf44_2, VG.Proof.Gcm.X86_64.StitchZ.shuf44_3, VG.Proof.Gcm.X86_64.StitchZ.State.zlane_setV256, State.zlane_setV_ne,
    reduceCtorEq, ↓reduceIte, Nat.one_ne_zero, BitVec.getLsbD_ofNat]
  all_goals simp [State.lane, State.zlane, State.setV, pr4]

/-- Lane 0 of `r` in its four lanes. -/
theorem bcast_ok (r : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 r r r 1), .zop (.vshufi32x4 r r r 0x44)]) s fun t =>
      (∀ l < 4, t.zlane r l = s.xmm r) ∧ ZFrame [r] s t := by
  refine WP.mono (WP.zframe (rs := [r]) (by simp [vecDst, VOp.dst?, ZOp.dst])
    (Q := fun t => ∀ l < 4, t.zlane r l = s.xmm r) ?_) fun t h => h
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [VOp.exec, zlane_zbin, zlane_vshufi32x4 _ _ _ _ _ _ hl, ite_true]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals simp only [VG.Proof.Gcm.X86_64.StitchZ.shuf44_0, VG.Proof.Gcm.X86_64.StitchZ.shuf44_1,
    VG.Proof.Gcm.X86_64.StitchZ.shuf44_2, VG.Proof.Gcm.X86_64.StitchZ.shuf44_3]
  all_goals simp [State.lane, State.zlane, State.setV]

/-- The mask and the reduction constant in every lane of `zmm0` and `zmm1`. -/
theorem pow4c_ok (s : State) :
    WP isa (.block (([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] : List Instr) ++
        ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr))) s fun t =>
      (∀ l < 4, t.zlane .xmm0 l = s.xmm .xmm0) ∧ (∀ l < 4, t.zlane .xmm1 l = s.xmm .xmm1) ∧
      ZFrame [.xmm0, .xmm1] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (bcast_ok .xmm0 s) fun t₁ ⟨b₁, f₁⟩ => WP.mono (bcast_ok .xmm1 t₁) fun t ⟨b, f⟩ => ⟨fun l hl => ?_,
    fun l hl => ?_, (f₁.mono (rs' := [.xmm0, .xmm1]) (by simp)).trans (f.mono (by simp))⟩
  · rw [f.zlane _ (by decide) l hl, b₁ l hl]
  · rw [b l hl]
    have := f₁.zlane .xmm1 (by decide) 0 (by decide)
    simpa [State.zlane, State.lane] using this

/-- Group `j` of the table at `T` holds its powers of `H`. -/
def GrpOk (m : Mem) (T : Addr) (H : Block) (j : Nat) : Prop :=
  ∀ l < 4, x * φ (m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128) = φ H ^ (4 * j + 4 - l)

/-- A group outside a 64-byte write is kept. -/
theorem GrpOk.keep {m m' : Mem} {T : Addr} {H : Block} {i j : Nat} (h : GrpOk m T H j)
    (f : Frame [⟨T + BitVec.ofNat 64 (64 * i), 64⟩] m m') (hij : i ≠ j) (hi : i < 8) (hj : j < 8) :
    GrpOk m' T H j := fun l hl => by
  rw [f.readW (r := ⟨T + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint T (by omega) (by omega) (by omega)) (by decide)]
  exact h l hl

/-- `powLoad d k`: group `k + d / 64` from group `k`, times `zmm12`, whose
lanes are `Tₑ`. -/
theorem powLoadG_ok {T : Addr} {H : Block} {d k e : Nat} (hd : d = 64 * (e / 4)) (he : e % 4 = 0)
    (hk : k + d / 64 < 8) (s : State) (hr11 : s.gpr .r11 = T)
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) (hB : ∀ l < 4, x * φ (s.zlane .xmm12 l) = φ H ^ e)
    (hG : GrpOk s.mem T H k) (hin : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (64 * k)) 64)
    (hout : InRegions s.wr (T + BitVec.ofNat 64 (d + 64 * k)) 64) :
    WP isa (.block (VG.Impl.Gcm.X86_64.StitchZ.powLoad d k)) s fun t =>
      GrpOk t.mem T H (k + d / 64) ∧ Frame [⟨T + BitVec.ofNat 64 (64 * (k + d / 64)), 64⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  have ea : ∀ n : Nat, s.gpr .r11 + BitVec.ofInt 64 ((n : Nat) : Int) = T + BitVec.ofNat 64 n := fun n => by
    rw [hr11, BitVec.ofInt_natCast]
  have hdk : d + 64 * k = 64 * (k + d / 64) := by omega
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.powLoad_ok d k s h1 (by rw [ea]; exact hin) (by rw [ea]; exact hout))
    fun t ⟨⟨v, mt, hv⟩, gt, rdt, wrt, zt⟩ => ⟨fun l hl => ?_, ?_, gt, rdt, wrt, zt⟩
  · have ha : T + BitVec.ofNat 64 (64 * (k + d / 64) + 16 * l) =
        T + BitVec.ofNat 64 (d + 64 * k) + BitVec.ofNat 64 (16 * l) := by
      rw [add_ofNat_ofNat, show d + 64 * k + 16 * l = 64 * (k + d / 64) + 16 * l by omega]
    rw [mt, ea, ha]
    have e := readW_writeW_inside s.mem (T + BitVec.ofNat 64 (d + 64 * k)) v (k := 16 * l) (n := 16)
      (by omega) (by decide)
    rw [show 8 * 16 = 128 from rfl, show 8 * (16 * l) = 128 * l by omega] at e
    rw [e, hv l hl, ea, add_ofNat_ofNat, VG.Proof.Gcm.X86_64.StitchZ.φ_lanemul (hG l hl) (hB l hl)]
    congr 1; omega
  · rw [mt, ea, hdk]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

/-- While `powMore` runs: `n` groups of the table at `T`, written only in
the table, and the registers it does not write. -/
structure PI (s₀ : State) (T : Addr) (H : Block) (n : Nat) (t : State) : Prop where
  tab : TabF t.mem T H n
  frame : Frame [⟨T, 512⟩] s₀.mem t.mem
  gpr : t.gpr = s₀.gpr
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  z0 : ∀ l < 4, t.zlane .xmm0 l = s₀.zlane .xmm0 l
  z1 : ∀ l < 4, t.zlane .xmm1 l = s₀.zlane .xmm1 l

/-- Group `n` from group `k` (`powLoad d k`, `n = k + d / 64`). -/
theorem powLoadT_ok {s₀ : State} {T : Addr} {H : Block} {d k e n : Nat} (hd : d = 64 * (e / 4)) (he : e % 4 = 0)
    (hkn : k < n) (hn : n = k + d / 64) (hn8 : n < 8) (t : State) (hI : PI s₀ T H n t)
    (hr11 : t.gpr .r11 = T) (hB : ∀ l < 4, x * φ (t.zlane .xmm12 l) = φ H ^ e)
    (h1 : ∀ l < 4, s₀.zlane .xmm1 l = poly) (hw : Covers [⟨T, 512⟩] s₀.wr) :
    WP isa (.block (VG.Impl.Gcm.X86_64.StitchZ.powLoad d k)) t fun t' =>
      PI s₀ T H (n + 1) t' ∧ ∀ l < 4, t'.zlane .xmm12 l = t.zlane .xmm12 l := by
  have hwt : Covers [⟨T, 512⟩] t.wr := by rw [hI.wr]; exact hw
  refine WP.mono (powLoadG_ok hd he (by omega) t hr11 (fun l hl => by rw [hI.z1 l hl, h1 l hl]) hB
    (hI.tab k hkn) (in_left (in_off hwt (by omega) (by decide)))
    (in_off hwt (by omega) (by decide))) fun t' ⟨g', f', gp', rd', wr', z'⟩ => ⟨⟨fun j hj => ?_, ?_,
      by rw [gp', hI.gpr], by rw [rd', hI.rd], by rw [wr', hI.wr], fun l hl => by rw [z' _ (by decide) (by decide)
      (by decide) (by decide) (by decide) l hl, hI.z0 l hl], fun l hl => by rw [z' _ (by decide) (by decide)
      (by decide) (by decide) (by decide) l hl, hI.z1 l hl]⟩,
    fun l hl => z' _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl⟩
  · by_cases hjn : j = n
    · subst hjn; rw [hn]; exact g'
    · exact GrpOk.keep (hI.tab j (by omega)) (i := n) (by rw [hn]; exact f') (by omega) (by omega) (by omega)
  · exact hI.frame.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base T (by omega)⟩)

/-- The broadcast of a power from the table into `zmm12`. -/
theorem bcastT_ok {s₀ : State} {T : Addr} {H : Block} {n j : Nat} (hj : j < n) (t : State)
    (hI : PI s₀ T H n t) (hr11 : t.gpr .r11 = T) (hw : Covers [⟨T, 512⟩] s₀.wr) (hj8 : j < 8) :
    WP isa (.block [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * j))]) t fun t' =>
      PI s₀ T H n t' ∧ (∀ l < 4, x * φ (t'.zlane .xmm12 l) = φ H ^ (4 * j + 4)) := by
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 (64 * j)) 16 := by
    rw [hr11, hI.rd, hI.wr]; exact in_left (in_off hw (by omega) (by decide))
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.Gcm.X86_64.StitchZ.bcast_exec .xmm12 .r11 (64 * j) t hin, WP.block_nil ⟨?_, fun l hl => ?_⟩⟩
  · exact ⟨hI.tab, hI.frame, hI.gpr, hI.rd, hI.wr,
      fun l hl => by rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, hI.z0 l hl],
      fun l hl => by rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, hI.z1 l hl]⟩
  · rw [VG.Proof.Gcm.X86_64.StitchZ.zlane_bcast _ _ _ hl, hr11]
    have := hI.tab j hj 0 (by decide)
    rwa [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at this

theorem PI.mono {s₀ : State} {T : Addr} {H : Block} {n m : Nat} {t : State} (h : PI s₀ T H n t) (hm : m ≤ n) :
    PI s₀ T H m t :=
  ⟨fun j hj => h.tab j (by omega), h.frame, h.gpr, h.rd, h.wr, h.z0, h.z1⟩

/-- `cmp rax, k` in `powMore`. -/
theorem cmpRax_ok {s₀ : State} {T : Addr} {H : Block} {n g k : Nat} (t : State) (hI : PI s₀ T H n t)
    (hrax : t.gpr .rax = BitVec.ofNat 64 (4 * g)) (hg : g ≤ 8) (hk : k < 2 ^ 31) :
    WP isa (.block [.alu .cmp .rax (imm k)]) t fun t' =>
      t'.cf = some (decide (4 * g < k)) ∧ PI s₀ T H n t' ∧ (∀ l < 4, t'.zlane .xmm12 l = t.zlane .xmm12 l) := by
  apply WP.of_runBlock
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm]; rfl,
    ?_, ?_, ?_⟩
  · rw [cf_arithFlags, hrax, imm_eq hk, toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega)]
  · exact ⟨hI.tab, hI.frame, hI.gpr, hI.rd, hI.wr, hI.z0, hI.z1⟩
  · exact fun _ _ => rfl

/-- The groups of powers after the first, as far as `m' = 4 g` needs. -/
theorem powMore_ok {s₀ : State} {T : Addr} {H : Block} {g : Nat} (hg1 : 1 ≤ g) (hg : g ≤ 8) (t : State)
    (hI : PI s₀ T H 1 t) (hr11 : t.gpr .r11 = T) (hrax : t.gpr .rax = BitVec.ofNat 64 (4 * g))
    (h1 : ∀ l < 4, s₀.zlane .xmm1 l = poly) (hw : Covers [⟨T, 512⟩] s₀.wr) :
    WP isa powMore t (PI s₀ T H g) := by
  have r11 : ∀ {n} {t' : State}, PI s₀ T H n t' → t'.gpr .r11 = T := fun h => by rw [h.gpr, ← hI.gpr, hr11]
  have rax : ∀ {n} {t' : State}, PI s₀ T H n t' → t'.gpr .rax = BitVec.ofNat 64 (4 * g) := fun h => by
    rw [h.gpr, ← hI.gpr, hrax]
  refine WP.seq (WP.mono (cmpRax_ok t hI hrax hg (by decide)) fun t₁ ⟨c₁, I₁, _⟩ => ?_)
  refine WP.ite (decide (4 * g < 5)) (by simp only [eval, c₁]) (fun h => WP.block_nil (I₁.mono ?_)) fun h => ?_
  · have := of_decide_eq_true h; omega
  have h₁ : 2 ≤ g := by have := of_decide_eq_false h; omega
  -- `H'⁸`–`H'⁵`.
  rw [show ([.vbroadcasti32x4 .xmm12 (at_ .r11 0)] ++ VG.Impl.Gcm.X86_64.StitchZ.powLoad 64 0 ++
      [.alu .cmp .rax (imm 9)] : List Instr) = [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * 0))] ++
      (VG.Impl.Gcm.X86_64.StitchZ.powLoad 64 0 ++ [.alu .cmp .rax (imm 9)]) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastT_ok (by decide) t₁ I₁ (r11 I₁) hw (by decide)) fun t₂ ⟨I₂, b₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 4) rfl rfl (by decide) rfl (by decide) t₂ I₂ (r11 I₂) b₂ h1 hw)
    fun t₃ ⟨I₃, _⟩ => ?_
  refine WP.mono (cmpRax_ok t₃ I₃ (rax I₃) hg (by decide)) fun t₄ ⟨c₄, I₄, _⟩ => ?_
  refine WP.ite (decide (4 * g < 9)) (by simp only [eval, c₄]) (fun h => WP.block_nil (I₄.mono ?_)) fun h => ?_
  · have := of_decide_eq_true h; omega
  have h₂ : 3 ≤ g := by have := of_decide_eq_false h; omega
  -- `H'¹⁶`–`H'⁹`.
  rw [show ([.vbroadcasti32x4 .xmm12 (at_ .r11 64)] ++
      (List.range 2).flatMap (VG.Impl.Gcm.X86_64.StitchZ.powLoad 128) ++ [.alu .cmp .rax (imm 17)] : List Instr) =
      [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * 1))] ++ (VG.Impl.Gcm.X86_64.StitchZ.powLoad 128 0 ++
      (VG.Impl.Gcm.X86_64.StitchZ.powLoad 128 1 ++ [.alu .cmp .rax (imm 17)])) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastT_ok (by decide) t₄ I₄ (r11 I₄) hw (by decide)) fun t₅ ⟨I₅, b₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 8) rfl rfl (by decide) rfl (by decide) t₅ I₅ (r11 I₅) b₅ h1 hw)
    fun t₆ ⟨I₆, z₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 8) rfl rfl (by decide) rfl (by decide) t₆ I₆ (r11 I₆)
    (fun l hl => by rw [z₆ l hl]; exact b₅ l hl) h1 hw) fun t₇ ⟨I₇, _⟩ => ?_
  refine WP.mono (cmpRax_ok t₇ I₇ (rax I₇) hg (by decide)) fun t₈ ⟨c₈, I₈, _⟩ => ?_
  refine WP.ite (decide (4 * g < 17)) (by simp only [eval, c₈]) (fun h => WP.block_nil (I₈.mono ?_)) fun h => ?_
  · have := of_decide_eq_true h; omega
  -- `H'³²`–`H'¹⁷`.
  rw [show (.vbroadcasti32x4 .xmm12 (at_ .r11 192) ::
      (List.range 4).flatMap (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256) : List Instr) =
      [.vbroadcasti32x4 .xmm12 (at_ .r11 (64 * 3))] ++ (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 0 ++
      (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 1 ++ (VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 2 ++
      VG.Impl.Gcm.X86_64.StitchZ.powLoad 256 3))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (bcastT_ok (by decide) t₈ I₈ (r11 I₈) hw (by decide)) fun u₁ ⟨J₁, b₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₁ J₁ (r11 J₁) b₁ h1 hw)
    fun u₂ ⟨J₂, z₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₂ J₂ (r11 J₂)
    (fun l hl => by rw [z₂ l hl]; exact b₁ l hl) h1 hw) fun u₃ ⟨J₃, z₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₃ J₃ (r11 J₃)
    (fun l hl => by rw [z₃ l hl, z₂ l hl]; exact b₁ l hl) h1 hw) fun u₄ ⟨J₄, z₄⟩ => ?_
  refine WP.mono (powLoadT_ok (e := 16) rfl rfl (by decide) rfl (by decide) u₄ J₄ (r11 J₄)
    (fun l hl => by rw [z₄ l hl, z₃ l hl, z₂ l hl]; exact b₁ l hl) h1 hw) fun u₅ ⟨J₅, _⟩ => J₅.mono hg

/-- Group 0 stored. -/
theorem store8_ok (t : State) {T : Addr} (hr11 : t.gpr .r11 = T) (hw : InRegions t.wr T 64) :
    WP isa (.block [.vmovdqu32Store (at_ .r11 0) .xmm8]) t fun t' =>
      t'.mem = t.mem.writeW T (t.zmm .xmm8) ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ∀ r l, t'.zlane r l = t.zlane r l := by
  have e : t.gpr .r11 + BitVec.ofInt 64 ((0 : Nat) : Int) = T := by rw [hr11, BitVec.ofInt_natCast, BitVec.add_zero]
  rw [WP.block_cons_iff]
  refine ⟨_, by simp only [isa, exec, State.store512_eq, State.ea, at_, e, hw, ite_true]; rfl, WP.block_nil ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The table of powers of the hash subkey, `m' = 4 g` of them at least, at
`W + 1536`. -/
theorem powers_ok {Ctx W SP : Addr} {g : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) (hg1 : 1 ≤ g) (hg : g ≤ 8) :
    WP isa powers s fun t =>
      TabOk t.mem (W + BitVec.ofNat 64 1536) (Spec.Gcm.ctxH s.mem Ctx) g ∧
      Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem t.mem ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hT : Covers [⟨W + BitVec.ofNat 64 1536, 512⟩] s.wr := he.perm.wC (by decide)
  have e240 : s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int) = Ctx + BitVec.ofNat 64 240 := by
    rw [he.r13, BitVec.ofInt_natCast]
  rw [powers, show powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ [.mov .rax (.mem (at_ .r15 mpO))] =
    powSse ++ (ptr .r11 .r15 tbO ++ ([.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
      .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44)] ++ ([.vmovdqu32Store (at_ .r11 0) .xmm8] ++
      (([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] ++
        [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)]) ++
      [.mov .rax (.mem (at_ .r15 mpO))])))) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (powSse_ok s (by rw [e240]; exact he.perm.ctxR (by decide)))
    fun s₁ ⟨x0, x1, H1, H2, H3, H4, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [e240, ← VG.Proof.AesGcm.X86_64.ctxH_eq] at H1 H2 H3 H4
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, r11₂, g₂, m₂, rd₂, wr₂, x₂⟩ : ∃ s₂, runBlock isa (ptr .r11 .r15 tbO) s₁ = some s₂ ∧
      s₂.gpr .r11 = W + BitVec.ofNat 64 1536 ∧ (∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ ∀ r l, s₂.zlane r l = s₁.zlane r l := by
    refine ⟨_, by xrun [tbO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, g₁ _ (by decide : Reg.r15 ≠ .rax), he.r15]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals first | rfl | exact fun _ _ => rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (pow4a_ok s₂) fun s₃ ⟨z8, f₃⟩ => ?_
  rw [WP.block_append_iff]
  have hT₃ : InRegions s₃.wr (W + BitVec.ofNat 64 1536) 64 := by
    rw [f₃.wr, wr₂, wr₁]; exact he.perm.wW (by decide)
  refine WP.mono (store8_ok s₃ (by rw [f₃.gpr, r11₂]) hT₃) fun s₄ ⟨m₄, g₄, rd₄, wr₄, z₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow4c_ok s₄) fun s₅ ⟨c0, c1, f₅⟩ => ?_
  obtain ⟨s₆, run₆, rax₆, g₆, m₆, rd₆, wr₆, z₆⟩ : ∃ s₆, runBlock isa [.mov .rax (.mem (at_ .r15 mpO))] s₅ = some s₆ ∧
      s₆.gpr .rax = BitVec.ofNat 64 (4 * g) ∧ (∀ r, r ≠ .rax → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧
      s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr ∧ ∀ r l, s₆.zlane r l = s₅.zlane r l := by
    have r15₅ : s₅.gpr .r15 = W := by
      rw [f₅.gpr, g₄, f₃.gpr, g₂ _ (by decide), g₁ _ (by decide), he.r15]
    have mm : s₅.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) := by
      rw [f₅.mem, m₄, ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s₃.zmm .xmm8)
        (Region.contains_self _ _)).readW (r := ⟨W + BitVec.ofNat 64 288, 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
        f₃.mem, m₂, m₁, hmp]
    have r288 : InRegions (s₅.rd ++ s₅.wr) (W + BitVec.ofNat 64 288) 8 := by
      rw [f₅.rd, f₅.wr, rd₄, wr₄, f₃.rd, f₃.wr, rd₂, wr₂, rd₁, wr₁]; exact he.perm.wR (by decide)
    refine ⟨_, by xrun [r15₅, mm, r288, mpO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals first | rfl | exact fun _ _ => rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- Group 0 of the table, and what `powMore` keeps.
  have hw₆ : Covers [⟨W + BitVec.ofNat 64 1536, 512⟩] s₆.wr := by
    rw [wr₆, f₅.wr, wr₄, f₃.wr, wr₂, wr₁]; exact hT
  have x2 : ∀ r, s₂.xmm r = s₁.xmm r := fun r => x₂ r 0
  have I₆ : PI s₆ (W + BitVec.ofNat 64 1536) (Spec.Gcm.ctxH s.mem Ctx) 1 s₆ := by
    refine ⟨fun j hj l hl => ?_, Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    have hj0 : j = 0 := by omega
    subst hj0
    have e := readW_writeW_inside s₃.mem (W + BitVec.ofNat 64 1536) (s₃.zmm .xmm8) (k := 16 * l) (n := 16)
      (by omega) (by decide)
    rw [show 8 * 16 = 128 from rfl, show 8 * (16 * l) = 128 * l by omega] at e
    rw [m₆, f₅.mem, m₄, Nat.mul_zero, Nat.zero_add, e, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl, z8 l hl, x2]
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · exact H4
    · exact H3
    · exact H2
    · rw [show 4 * 0 + 4 - 3 = 1 from rfl, pow_one]; exact H1
  have xs : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → s₄.xmm r = s₁.xmm r := fun r h8 h9 => by
    rw [show s₄.xmm r = s₄.zlane r 0 from rfl, z₄, f₃.zlane r (by simp [h8, h9]) 0 (by decide)]
    exact x2 r
  refine WP.mono (powMore_ok hg1 hg s₆ I₆
    (by rw [g₆ _ (by decide), f₅.gpr, g₄, f₃.gpr, r11₂]) rax₆
    (fun l hl => by rw [z₆, c1 l hl, xs _ (by decide) (by decide), x1]) hw₆)
    fun t I => ⟨tabOk_of_F I.tab, ?_, fun l hl => ?_, fun l hl => ?_, fun r ha hb => ?_, ?_, ?_⟩
  · have f₄ : Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem s₆.mem := by
      rw [m₆, f₅.mem, m₄, ← m₁, ← m₂, ← f₃.mem]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s₃.zmm .xmm8)
        (Region.contains_self _ _)).sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
    exact f₄.trans I.frame
  · rw [I.z0 l hl, z₆, c0 l hl, xs _ (by decide) (by decide), x0]
  · rw [I.z1 l hl, z₆, c1 l hl, xs _ (by decide) (by decide), x1]
  · rw [I.gpr, g₆ r ha, f₅.gpr, g₄, f₃.gpr, g₂ r hb, g₁ r ha]
  · rw [I.rd, rd₆, f₅.rd, rd₄, f₃.rd, rd₂, rd₁]
  · rw [I.wr, wr₆, f₅.wr, wr₄, f₃.wr, wr₂, wr₁]

/-- `powers`' first block: `r11` at the table and `rax` the powers needed. -/
theorem powHead_ok {Ctx W SP : Addr} {g : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) :
    WP isa (.block (powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ ([.mov .rax (.mem (at_ .r15 mpO))] : List Instr))) s
      fun t =>
      t.gpr .rax = BitVec.ofNat 64 (4 * g) ∧ t.gpr .r11 = W + BitVec.ofNat 64 1536 := by
  have e240 : s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int) = Ctx + BitVec.ofNat 64 240 := by
    rw [he.r13, BitVec.ofInt_natCast]
  rw [show powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ [.mov .rax (.mem (at_ .r15 mpO))] =
    powSse ++ (ptr .r11 .r15 tbO ++ ([.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
      .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44)] ++ ([.vmovdqu32Store (at_ .r11 0) .xmm8] ++
      (([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] ++
        [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)]) ++
      [.mov .rax (.mem (at_ .r15 mpO))])))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (powSse_ok s (by rw [e240]; exact he.perm.ctxR (by decide)))
    fun s₁ ⟨_, _, _, _, _, _, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, r11₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa (ptr .r11 .r15 tbO) s₁ = some s₂ ∧
      s₂.gpr .r11 = W + BitVec.ofNat 64 1536 ∧ (∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [tbO], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, g₁ _ (by decide : Reg.r15 ≠ .rax), he.r15]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (pow4a_ok s₂) fun s₃ ⟨_, f₃⟩ => ?_
  rw [WP.block_append_iff]
  have hT₃ : InRegions s₃.wr (W + BitVec.ofNat 64 1536) 64 := by
    rw [f₃.wr, wr₂, wr₁]; exact he.perm.wW (by decide)
  refine WP.mono (store8_ok s₃ (by rw [f₃.gpr, r11₂]) hT₃) fun s₄ ⟨m₄, g₄, rd₄, wr₄, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow4c_ok s₄) fun s₅ ⟨_, _, f₅⟩ => ?_
  have r15₅ : s₅.gpr .r15 = W := by
    rw [f₅.gpr, g₄, f₃.gpr, g₂ _ (by decide), g₁ _ (by decide), he.r15]
  have mm : s₅.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) := by
    rw [f₅.mem, m₄, ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s₃.zmm .xmm8)
      (Region.contains_self _ _)).readW (r := ⟨W + BitVec.ofNat 64 288, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
      f₃.mem, m₂, m₁, hmp]
  have r288 : InRegions (s₅.rd ++ s₅.wr) (W + BitVec.ofNat 64 288) 8 := by
    rw [f₅.rd, f₅.wr, rd₄, wr₄, f₃.rd, f₃.wr, rd₂, wr₂, rd₁, wr₁]; exact he.perm.wR (by decide)
  refine WP.of_runBlock ⟨_, by xrun [r15₅, mm, r288, mpO], ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, f₅.gpr, g₄, f₃.gpr, r11₂]

end VG.Proof.AesGcm.X86_64.Short
