import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

namespace VG.Proof.P256.EcdhJac.Setup
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64

structure Post (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c s₀
  d : sv c base s D = dv c s₀
  e : sv c base s E = ev c s₀
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64
  gpr : ∀r,r∉[.x0,.x1,.x2,.x5,.x16,.x17,.x19,.x20] → s.gpr r=s₀.gpr r
  unch : Unch base [(0,size)] s₀.mem s.mem
  rd : s.rd=s₀.rd

theorem setup_only_ok {c : Cfg} (hc : CfgOk c) {s₀ : State} (hp : SetupPre c s₀) :
    WP isa (.block (c.setupWith none)) s₀ (Post c s₀ (s₀.gpr .x4)) := by
  refine WP.mono (setup_ok hc (.inl rfl) hp) fun s₁ P => ?_
  have hc' : ∀ ix ∈ c.consts, sv c (s₀.gpr .x4) s₁ ix.1 = ix.2 := P.consts
  have fx : Fixed c (s₀.gpr .x4) s₀.gpr s₁.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (BM, c.mont c.C.b) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved⟩
  refine ⟨⟨P.scr,P.x20,P.keep.wr,fx⟩,?_,?_,?_,P.flag,?_,P.unch,P.keep.rd⟩
  · simpa only [shAt_K c (.inl rfl),Nat.shiftRight_zero] using P.k
  · simpa only [shAt,reduceCtorEq,ite_false,Nat.shiftRight_zero] using P.d
  · simpa only [shAt,reduceCtorEq,ite_false,Nat.shiftRight_zero] using P.e
  · intro r hr
    exact P.keep.gpr r (fun h => hr ((show ∀r∈[Reg.x0,.x1,.x2,.x5,.x17,.x20],r∈[Reg.x0,.x1,.x2,.x5,.x16,.x17,.x19,.x20] from by decide) r h))
end VG.Proof.P256.EcdhJac.Setup
