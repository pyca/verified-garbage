module

-- separate module: brainpoolP256r1's verification is its only importer, but it builds on both callees' proofs
-- (the windows' and the comb's), which then build in parallel with the rest of its imports
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.JointCombAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Joint
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.CombVerified
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.CombLit

/-!
# ECDSA verification over brainpoolP256r1 on RISC-V: `[u]G` by the comb and `[v]Q` by windows

`VerifyComb.Cfg.joint brainpoolp256r1` leaves in `R` a representative of `[u]G + [v]Q`
(`jointComb_ok`). The proof is the one of every curve with a comb, `JointCombAll.Kit.jointComb_ok`
(`Proof/Ecdsa/RISCV64/JointCombAll.lean`), from what `jkit` says of this one: the call of the
comb's multiplication of `G` (`combCall_ok`, by `Comb.mulG_rv`), with the comb's table, which code
without frames leaves alone (`wp_tab`), and the complete addition (`Joint.addPt_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.JointComb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Ecdsa.RISCV64.VerifyComb
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1 (W unit mulRVc MC)
open VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Joint (PtOk addPt_ok JPre jSl addW mul_zero')
open VG.Proof.Ecdh.RISCV64.BrainpoolP256r1 (TailConsts sv_unch sl_eq FL mulKW unch_of_mulKeeps coord_sv point_eq dq
  rep_of_represents wsCallR_ok)

open VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Comb (TabAt)
open VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Window (copyPt_ok)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-- Code without frames keeps the comb's table, apart from the regions it may write. -/
theorem wp_tab {cd : Prog isa} (hn : cd.noFrames = true) {s : State} {base : Addr} {Q : State → Prop}
    (hT : TabAt base s) (hwr : s.wr = [⟨base, 8192⟩]) (h : WP isa cd s Q) :
    WP isa cd s fun s' => Q s' ∧ TabAt base s' := by
  obtain ⟨t, s', he, hq⟩ := h
  obtain ⟨r, -, -, f⟩ := Exec.regions he hn
  exact ⟨t, s', he, hq, hT.of_frame (Exec.syms he) r f (by rw [hwr]; simpa using hT.disj)⟩

/-- What `zeroR` writes. -/
abbrev zW : List (Nat × Nat) :=
  [(brainpoolp256r1.sl RX, 32), (brainpoolp256r1.sl RY, 32), (brainpoolp256r1.sl RZ, 32), (brainpoolp256r1.sl BP, 32)]

/-- `R = [k]G` by the call of `vg_brainpoolp256r1_mul_g`, for `k` at `K`, with the
table its readable region. -/
theorem combCall_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hc : TailConsts base s) (hT : TabAt base s) :
    WP isa (Cfg.wsCall Comb.mulGBrainpoolP256r1Name Comb.mulGBrainpoolP256r1) s fun s' => Kp s s' ∧
      MC.ResultInRange (sv base s K) (Spec.Weierstrass.G W) base s.mem s'.mem := by
  rw [Cfg.wsCall]
  refine WP.seq (WP.seq (WP.cons (exec_addi (by decide)) (WP.block_nil ?_)))
  generalize hs₂ : s.write .a0 (s.gpr wb + BitVec.ofInt 64 0) = s₂
  obtain u₂ : Upd s s₂ .a0 (s.gpr wb + BitVec.ofInt 64 0) := hs₂ ▸ Upd.write _ _ _
  obtain sy₂ : s₂.syms = s.syms := by rw [← hs₂]; rfl
  obtain K₂ : Kp s s₂ := Kp.of_upd u₂
  obtain a0₂ : s₂.gpr .a0 = base := by rw [u₂.gpr, hw.s0]; simp
  obtain hcov : Covers [⟨base, 8192⟩] s₂.wr := VG.Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.wr]; exact hw.wr
  obtain htab : Covers [Comb.tabRegion s₂] s₂.rd := VG.Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.rd, Comb.tabRegion, sy₂]; exact hT.rd
  obtain e0 : (s₂.callEntry.withRegions [Comb.tabRegion s₂] [⟨base, 8192⟩]).gpr .a0 = base := by
    simp only [State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), a0₂]
  obtain em : (s₂.callEntry.withRegions [Comb.tabRegion s₂] [⟨base, 8192⟩]).mem = s.mem := by
    simp only [State.withRegions_mem, State.callEntry_mem, u₂.mem]
  have esy : (s₂.callEntry.withRegions [Comb.tabRegion s₂] [⟨base, 8192⟩]).syms = s.syms := sy₂
  refine WP.call (Comb.mulG_rv hL) (rd := [Comb.tabRegion s₂]) (wr := [⟨base, 8192⟩]) ?_ (Covers.append htab hcov)
    hcov (fun s₃ r₃ w₃ p₃ _ G₃ _ hp => ?_) Impl.Ecdsa.RISCV64.Comb.mulGBrainpoolP256r1_noFrames
  · refine ⟨rfl, by rw [e0]; rfl, by rw [e0]; exact hw.nowrap, by rw [e0]; exact hw.al, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, em]
      exact ⟨(coord_sv _ _ MP).trans hc.mp, (coord_sv _ _ ZERO).trans hc.zero,
        (coord_sv _ _ ONEP).trans hc.onep, (coord_sv _ _ AP).trans hc.ap, (coord_sv _ _ B3P).trans hc.b3p⟩
    · rw [em, esy]; exact hT.held
    · rw [esy]; exact hT.al
    · rw [esy]; exact hT.fit
    · rw [e0]; simp only [Comb.tabRegion]; rw [esy]; exact hT.disj
  -- `s0` from `s3`.
  refine wp_mv fun s₄ u₄ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₄.rd, r₃, K₂.rd], by rw [u₄.wr, w₃, K₂.wr],
    by rw [u₄.sp, p₃, K₂.sp]⟩, ?_⟩
  · by_cases h : r = .s0
    · subst h; rw [u₄.gpr, G₃ _ (by decide), K₂.gpr _ (by decide), h3, hw.s0]
    · rw [u₄.other _ h, G₃ _ hr, K₂.gpr _ hr]
  · have := hp
    simp only [Comb.mulGRVc, State.withRegions_mem] at this
    rw [e0] at this
    rw [show s₂.callEntry.mem = s.mem by rw [State.callEntry_mem, u₂.mem]] at this
    obtain hk : MC.scalar base s.mem = sv base s K := coord_sv _ _ K
    rw [hk] at this
    rw [u₄.mem]
    exact this

/-- What `joint` writes. -/
abbrev combW : List (Nat × Nat) :=
  [(brainpoolp256r1.sl K, 32), (brainpoolp256r1.sl RX, 32), (brainpoolp256r1.sl RY, 32)] ++ mulKW ++ zW ++
    [(brainpoolp256r1.sl GX, 32), (brainpoolp256r1.sl CPX, 32), (brainpoolp256r1.sl CPY, 32), (brainpoolp256r1.sl K, 32)] ++ mulKW ++ zW ++
    addW (brainpoolp256r1.pt TX TY TZ) ++ [(brainpoolp256r1.sl RX, 32), (brainpoolp256r1.sl RY, 32), (brainpoolp256r1.sl RZ, 32)]

theorem wsCall_noFrames {f : String} {b : Prog isa} (h : b.noFrames = true) : (Cfg.wsCall f b).noFrames = true :=
  JointCombAll.wsCall_noFrames h

/-- What the proof shared by every curve (`JointCombAll.lean`) needs of this one: ECDH's kit, the
comb's call with its table, and the complete addition of `R` and `P`. -/
def jkit : JointCombAll.Kit where
  toKit := VG.Proof.Ecdh.RISCV64.BrainpoolP256r1.kit
  gN := Comb.mulGBrainpoolP256r1Name
  gC := Comb.mulGBrainpoolP256r1
  Tab := TabAt
  tab_frame := fun hn => fun hT hwr h => wp_tab hn hT hwr h
  tab_unch := fun hT sy rd hW U => hT.of_unch sy rd hW U
  comb_ok := fun hL => fun hw h3 hc _ hT =>
    combCall_ok hL hw h3 ⟨hc.mp, hc.mn, hc.zero, hc.one, hc.onep, hc.ap, hc.b3p, hc.expp⟩ hT
  addW := addW (brainpoolp256r1.pt TX TY TZ)
  add_ok := fun hL => fun hw hc _ => fun hP hP' hp hq =>
    WP.mono (addPt_ok hL hw hc.ap hc.b3p (p := brainpoolp256r1.pt RX RY RZ) (q := brainpoolp256r1.pt GX CPX CPY)
        (o := brainpoolp256r1.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) hP hP' ⟨hp.rep, hp.x, hp.y, hp.z⟩
        ⟨hq.rep, hq.x, hq.y, hq.z⟩)
      fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

theorem jointComb_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} (hp : JPre base s Q)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hT : TabAt base s) (hwr : s.wr = [⟨base, 8192⟩])
    (hu : sv base s UU < W.n) (hv : sv base s VV < W.n) :
    WP isa (VerifyComb.Cfg.joint brainpoolp256r1 "vg_brainpoolp256r1_mul" mulBrainpoolP256r1 Comb.mulGBrainpoolP256r1Name Comb.mulGBrainpoolP256r1) s fun s' =>
      Kc s s' ∧ Unch base combW s.mem s'.mem ∧
      PtOk base s' (brainpoolp256r1.pt RX RY RZ) (Spec.Weierstrass.add (mul (sv base s UU) (Spec.Weierstrass.G W))
        (mul (sv base s VV) Q)) :=
  WP.mono (jkit.jointComb_ok hL hp.ws h3 ⟨hc.mp, hc.mn, hc.zero, hc.one, hc.onep, hc.ap, hc.b3p, hc.expp⟩ hT hwr
      hp.qx hp.qy hp.q hp.on hu hv)
    fun _ ⟨K, U, p⟩ => ⟨K, U.cover (by decide), ⟨p.rep, p.x, p.y, p.z⟩⟩

end VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.JointComb
