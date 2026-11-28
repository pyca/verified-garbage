module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopCtx
public import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Keccak
import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Frag
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkChain
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the message digest

Untrusted: everything here is checked by Lean. In `Ctx`, the moves of a
call's arguments (`movs_ok`); calls of `vg_keccak_absorb_scratch`,
`vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` on the state at
`oStream` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); and `hashM'`, which leaves
`H_msg(R, PK.seed, PK.root, M′)` at `oDigest` (`hash_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt stateAt absorb pad rates squeezeFrom Repr)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (Arg Arg.mov callA kabs kpad ksqz hashM' zeroState stk fCtx fCtxLen fMsg fLen)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.MlKem.X86_64 (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)

/-! ## Arguments -/

/-- The value an argument moves. -/
def argVal (t : State) : Arg → BitVec 64
  | .slot f => t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 f) 64
  | .slotOff f o => t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o
  | .scr o => t.gpr .rbx + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .sp => t.gpr .rsp
  | .ret => t.gpr .rax

/-- What the moves need of an argument. -/
def argOk : Arg → Prop
  | .slot f => f + 8 ≤ 72
  | .slotOff f o => f + 8 ≤ 72 ∧ o < 2 ^ 31
  | .scr o => o < 2 ^ 31
  | .imm v => v < 2 ^ 32
  | .sp => True
  | .ret => True

/-- The frame's slots are readable. -/
abbrev FrIn (t : State) : Prop := ∀ f, f + 8 ≤ 72 → InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 f) 8

theorem argVal_congr {t t' : State} (hm : t'.mem = t.mem) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hbx : t'.gpr .rbx = t.gpr .rbx) (hax : t'.gpr .rax = t.gpr .rax) (a : Arg) : argVal t' a = argVal t a := by
  cases a <;> simp only [argVal, hm, hsp, hbx, hax]

theorem mov_ok (d : Reg) (a : Arg) (ha : argOk a) (t : State)
    (hfr : FrIn t) {Q : State → Prop}
    (k : ∀ t1 : State, t1.gpr d = argVal t a → (∀ r, r ≠ d → t1.gpr r = t.gpr r) → t1.mem = t.mem →
      t1.rd = t.rd → t1.wr = t.wr → Q t1) :
    WP isa (.block (a.mov d)) t Q := by
  cases a with
  | slot f => exact wp_movm (by rw [ea_stk]) (hfr f ha) fun t1 u => WP.block_nil (k t1 u.gpr u.other u.mem u.rd u.wr)
  | slotOff f o =>
    refine wp_movm (by rw [ea_stk]) (hfr f ha.1) fun t1 u => wp_addi fun t2 v => WP.block_nil ?_
    refine k t2 (by rw [v.gpr, u.gpr, Levels.sx_ofNat ha.2]; rfl) (fun r hr => by rw [v.other _ hr, u.other _ hr])
      (by rw [v.mem, u.mem]) (by rw [v.rd, u.rd]) (by rw [v.wr, u.wr])
  | scr o =>
    refine wp_mov fun t1 u => wp_addi fun t2 v => WP.block_nil ?_
    refine k t2 (by rw [v.gpr, u.gpr, Levels.sx_ofNat ha]; rfl) (fun r hr => by rw [v.other _ hr, u.other _ hr])
      (by rw [v.mem, u.mem]) (by rw [v.rd, u.rd]) (by rw [v.wr, u.wr])
  | imm v =>
    refine wp_mov32i fun t1 u => WP.block_nil ?_
    exact k t1 (by rw [u.gpr, setw_ofNat32 ha]; rfl) u.other u.mem u.rd u.wr
  | sp => exact wp_mov fun t1 u => WP.block_nil (k t1 u.gpr u.other u.mem u.rd u.wr)
  | ret => exact wp_mov fun t1 u => WP.block_nil (k t1 u.gpr u.other u.mem u.rd u.wr)

theorem movs_ok : ∀ (ps : List (Reg × Arg)) (t : State),
    (∀ q ∈ ps, q.1 ≠ .rsp ∧ q.1 ≠ .rbx ∧ q.1 ≠ .rax ∧ argOk q.2) → (ps.map Prod.fst).Nodup → FrIn t →
    ∀ {Q : State → Prop}, (∀ t1 : State, (∀ q ∈ ps, t1.gpr q.1 = argVal t q.2) →
      (∀ r, r ∉ ps.map Prod.fst → t1.gpr r = t.gpr r) → t1.mem = t.mem → t1.rd = t.rd → t1.wr = t.wr → Q t1) →
    WP isa (.block (ps.flatMap fun (d, a) => a.mov d)) t Q
  | [], t, _, _, _, _, k => WP.block_nil (k t (fun _ h => absurd h List.not_mem_nil) (fun _ _ => rfl) rfl rfl rfl)
  | (d, a) :: ps, t, hok, hnd, hfr, _, k => by
    rw [List.flatMap_cons]
    obtain ⟨h1, h2, h3, ha⟩ := hok (d, a) (List.mem_cons_self ..)
    refine WP.block_append (mov_ok d a ha t hfr fun t1 e1 o1 m1 r1 w1 => ?_)
    have hnd' := List.nodup_cons.mp hnd
    have hfr1 : FrIn t1 := fun f hf => by rw [r1, w1, o1 _ (Ne.symm h1)]; exact hfr f hf
    refine movs_ok ps t1 (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hnd'.2 hfr1 fun t2 e2 o2 m2 r2 w2 => ?_
    have cg : ∀ b, argVal t1 b = argVal t b :=
      argVal_congr m1 (o1 _ (Ne.symm h1)) (o1 _ (Ne.symm h2)) (o1 _ (Ne.symm h3))
    refine k t2 (fun q hq => ?_) (fun r hr => ?_) (m2.trans m1) (r2.trans r1) (w2.trans w1)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o2 _ hnd'.1, e1]
      · rw [e2 q hq, cg]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o2 r hr.2, o1 r hr.1]

/-! ## Regions -/

/-- The stack below `SP`. -/
theorem below_SP {L : VL} {k : Nat} (hk : k ≤ L.st + 8) :
    below L.SP k = ⟨L.B + BitVec.ofNat 64 (L.st + 8 - k), k⟩ := by
  show (⟨L.SP - BitVec.ofNat 64 k, k⟩ : Region) = _
  congr 1
  rw [VL.SP, Offset.sub_ofNat_eq _ (a := k) (b := L.st + 8) hk, BitVec.add_sub_cancel]

theorem free_below {L : VL} (_hL : L.Ok) {k : Nat} (hk : k ≤ L.st + 8) : Free L (below L.SP k) := by
  rw [below_SP hk]
  exact .inr (Offset.sub_base _ (by omega))

/-- Parts of `scratch` from the nodes up to the saved registers. -/
theorem free_hi {L : VL} (hL : L.Ok) {o l : Nat} (h₁ : 12640 ≤ o) (h₂ : o + l ≤ 34080) : Free L ⟨at' L.S o, l⟩ := by
  have hn := hL.n32
  refine .inl ⟨hL.scr_sub (by omega), fun q hq => ?_⟩
  simp only [VL.prot, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hq
  rcases hq with ((rfl | rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩)
  · exact Levels.disj_scr L.S (by omega) (by omega) (by omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.oPkSeed, Layout.oKeys]; omega) (by omega)
      (by simp only [Layout.oPkSeed, Layout.oKeys]; omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.oPkRoot, Layout.oKeys]; omega) (by omega)
      (by simp only [Layout.oPkRoot, Layout.oKeys]; omega)
  · exact Levels.disj_scr L.S (by rw [show Impl.SlhDsa.X86_64.Shake.oKgSave = 34080 from rfl]; omega) (by omega)
      (by rw [show Impl.SlhDsa.X86_64.Shake.oKgSave = 34080 from rfl]; omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact Levels.disj_scr L.S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) (by omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)

namespace Ctx

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem} {t : State}

theorem frIn (hc : Ctx L g m₀ t) : FrIn t := fun f hf => by
  rw [hc.rsp]; exact hc.inFr hf

theorem regsIn (hc : Ctx L g m₀ t) : t.rd ++ t.wr = L.rd ++ [L.FR, L.SCR] := by rw [hc.rd, hc.wr]

/-- After the moves of a call's arguments. -/
theorem moved (hc : Ctx L g m₀ t) {t1 : State} (hr : ∀ r, r ∈ calleeSaved → t1.gpr r = t.gpr r)
    (hm : t1.mem = t.mem) (hrd : t1.rd = t.rd) (hwr : t1.wr = t.wr) : Ctx L g m₀ t1 :=
  hc.regs hrd hwr hm hr

/-- After a call that keeps the callee-saved registers and writes only free parts. -/
theorem called (hL : L.Ok) (hc : Ctx L g m₀ t) {t' : State} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, Free L r) : Ctx L g m₀ t' :=
  hc.of_frame hL hrd hwr (hcs .rsp (by decide)) (hcs .rbx (by decide)) (fun r hr _ _ => hcs r hr) hf hrs

end Ctx

/-! ## The sponge functions -/

/-- The Keccak state of `H_msg`, and the sponge functions' working space. -/
abbrev VL.ST (L : VL) : Addr := at' L.S Layout.oStream
abbrev VL.KS (L : VL) : Addr := at' L.S (Layout.oStream + 200)

theorem oStream_eq : Layout.oStream = 30560 := rfl

theorem sponge_facts {L : VL} (hL : L.Ok) :
    Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ ∧ (below L.SP 16).Disjoint ⟨L.ST, 200⟩ ∧
      (below L.SP 16).Disjoint ⟨L.KS, 640⟩ ∧ Free L ⟨L.ST, 200⟩ ∧ Free L ⟨L.KS, 640⟩ ∧ Free L (below L.SP 16) ∧
      Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] [L.FR, L.SCR] := by
  have hst := hL.st16
  have hb : Region.Sub (below L.SP 16) L.CS := by rw [below_SP (by omega)]; exact Offset.sub_base _ (by omega)
  refine ⟨Levels.disj_scr L.S (by omega) (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega),
    (hL.cs_scr.sub_left hb).sub_right (hL.scr_sub (by rw [oStream_eq]; omega)),
    (hL.cs_scr.sub_left hb).sub_right (hL.scr_sub (by rw [oStream_eq]; omega)),
    free_hi hL (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega),
    free_hi hL (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega), free_below hL (by omega), ?_⟩
  refine Covers.of_sub fun r hr => ⟨L.SCR, by simp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨Layout.oStream, rfl, by rw [oStream_eq]; simp⟩
  · exact ⟨Layout.oStream + 200, rfl, by rw [oStream_eq]; simp⟩

theorem covers_frs (L : VL) : Covers [L.FR, L.SCR] (L.rd ++ [L.FR, L.SCR]) :=
  Covers.of_mem fun _ hr => List.mem_append_right _ hr

theorem callee_saved_args : ∀ r ∈ calleeSaved, r ∉ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9] := by decide
theorem callee_saved_args5 : ∀ r ∈ calleeSaved, r ∉ [Reg.rdi, .rsi, .rdx, .rcx, .r8] := by decide

theorem args_ok6 (a b c d e f : Arg) (ha : argOk a) (hb : argOk b) (hc : argOk c) (hd : argOk d) (he : argOk e)
    (hf : argOk f) : ∀ q ∈ [(Reg.rdi, a), (.rsi, b), (.rdx, c), (.rcx, d), (.r8, e), (.r9, f)],
      q.1 ≠ .rsp ∧ q.1 ≠ .rbx ∧ q.1 ≠ .rax ∧ argOk q.2 := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp, by simp, by assumption⟩

theorem argsIn6 {t t1 : State} {a b c d e f : Arg}
    (h : ∀ q ∈ [(Reg.rdi, a), (.rsi, b), (.rdx, c), (.rcx, d), (.r8, e), (.r9, f)], t1.gpr q.1 = argVal t q.2) :
    t1.gpr .rdi = argVal t a ∧ t1.gpr .rsi = argVal t b ∧ t1.gpr .rdx = argVal t c ∧ t1.gpr .rcx = argVal t d ∧
      t1.gpr .r8 = argVal t e ∧ t1.gpr .r9 = argVal t f :=
  ⟨h (.rdi, a) (by simp), h (.rsi, b) (by simp), h (.rdx, c) (by simp), h (.rcx, d) (by simp), h (.r8, e) (by simp),
    h (.r9, f) (by simp)⟩

theorem argsIn5 {t t1 : State} {a b c d e : Arg}
    (h : ∀ q ∈ [(Reg.rdi, a), (.rsi, b), (.rdx, c), (.rcx, d), (.r8, e)], t1.gpr q.1 = argVal t q.2) :
    t1.gpr .rdi = argVal t a ∧ t1.gpr .rsi = argVal t b ∧ t1.gpr .rdx = argVal t c ∧ t1.gpr .rcx = argVal t d ∧
      t1.gpr .r8 = argVal t e :=
  ⟨h (.rdi, a) (by simp), h (.rsi, b) (by simp), h (.rdx, c) (by simp), h (.rcx, d) (by simp), h (.r8, e) (by simp)⟩

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The moves of `vg_keccak_absorb_scratch`'s arguments. -/
theorem kabs_mv (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {src len pos : Arg} (h1 : argOk src) (h2 : argOk len)
    (h3 : argOk pos) {dp : Addr} {N q : Nat} (hdp : argVal t src = dp) (hN : argVal t len = BitVec.ofNat 64 N)
    (hq : argVal t pos = BitVec.ofNat 64 q) (hql : q < 136) (hNl : N < 2 ^ 64)
    (hin : InRegions (L.rd ++ [L.FR, L.SCR]) dp N) (dS : Region.Disjoint ⟨dp, N⟩ ⟨L.ST, 840⟩)
    (kD : (below L.SP 16).Disjoint ⟨dp, N⟩) :
    WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, src, len,
      .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t fun t1 => Ctx L g m₀ t1 ∧
      t1.mem = t.mem ∧ AbsorbArgs t1 L.ST dp L.KS 136 q N ∧
      Covers ([⟨dp, N⟩] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) ∧ Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr := by
  obtain ⟨fs, ks, kk, fST, fKS, fB, cv⟩ := sponge_facts hL
  rw [show [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, src, len,
      .scr (Layout.oStream + 200)] = [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos), (.rcx, src),
      (.r8, len), (.r9, .scr (Layout.oStream + 200))] from rfl]
  refine (movs_ok _ t (args_ok6 _ _ _ _ _ _ (by show _ < _; rw [oStream_eq]; omega) (by show _ < _; omega)
    h3 h1 h2 (by show _ < _; rw [oStream_eq]; omega)) (by show List.Nodup [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9]; decide) hc.frIn fun t1 hv ho hm hr hw => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.moved (fun r h => ho r (callee_saved_args r h)) hm hr hw
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := argsIn6 hv
  have hsp : t1.gpr .rsp = L.SP := hc1.rsp
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q N :=
    ⟨by rw [v1]; simp only [argVal, hc.rbx], by rw [v2]; rfl,
      by rw [v3, hq], by rw [v4, hdp], by rw [v5, hN],
      by rw [v6]; simp only [argVal, hc.rbx], by decide, hql, hNl, fs,
      dS.sub_right (Region.sub_prefix (by omega)),
      dS.sub_right (Offset.sub L.S (by omega) (by omega)),
      by rw [hsp]; exact ks, by rw [hsp]; exact kD, by rw [hsp]; exact kk⟩
  have hcov : Covers ([⟨dp, N⟩] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) := by
    rw [hc1.regsIn]
    exact Covers.append_left (Covers.one hin) (Covers.trans cv (covers_frs L))
  have hcovw : Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr := by rw [hc1.wr]; exact cv
  exact ⟨hc1, hm, ha, hcov, hcovw⟩

theorem kabs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {src len pos : Arg} (h1 : argOk src) (h2 : argOk len)
    (h3 : argOk pos) {dp : Addr} {N q : Nat} (hdp : argVal t src = dp) (hN : argVal t len = BitVec.ofNat 64 N)
    (hq : argVal t pos = BitVec.ofNat 64 q) (hql : q < 136) (hNl : N < 2 ^ 64)
    (hin : InRegions (L.rd ++ [L.FR, L.SCR]) dp N) (dS : Region.Disjoint ⟨dp, N⟩ ⟨L.ST, 840⟩)
    (kD : (below L.SP 16).Disjoint ⟨dp, N⟩) :
    WP isa (kabs src len pos) t fun t' => Ctx L g m₀ t' ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 → Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp N)) ∧
      (t'.gpr .rax).toNat = (q + N) % 136 := by
  obtain ⟨fs, ks, kk, fST, fKS, fB, cv⟩ := sponge_facts hL
  unfold kabs callA
  rw [show [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, src, len,
      .scr (Layout.oStream + 200)] = [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos), (.rcx, src),
      (.r8, len), (.r9, .scr (Layout.oStream + 200))] from rfl]
  refine WP.seq (movs_ok _ t (args_ok6 _ _ _ _ _ _ (by show _ < _; rw [oStream_eq]; omega) (by show _ < _; omega)
    h3 h1 h2 (by show _ < _; rw [oStream_eq]; omega)) (by show List.Nodup [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9]; decide) hc.frIn fun t1 hv ho hm hr hw => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.moved (fun r h => ho r (callee_saved_args r h)) hm hr hw
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := argsIn6 hv
  have hsp : t1.gpr .rsp = L.SP := hc1.rsp
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q N :=
    ⟨by rw [v1]; simp only [argVal, hc.rbx], by rw [v2]; rfl,
      by rw [v3, hq], by rw [v4, hdp], by rw [v5, hN],
      by rw [v6]; simp only [argVal, hc.rbx], by decide, hql, hNl, fs,
      dS.sub_right (Region.sub_prefix (by omega)),
      dS.sub_right (Offset.sub L.S (by omega) (by omega)),
      by rw [hsp]; exact ks, by rw [hsp]; exact kD, by rw [hsp]; exact kk⟩
  have hcov : Covers ([⟨dp, N⟩] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) := by
    rw [hc1.regsIn]
    exact Covers.append_left (Covers.one hin) (Covers.trans cv (covers_frs L))
  have hcovw : Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr := by rw [hc1.wr]; exact cv
  refine absorb_call ha hcov hcovw fun s' hrd hwr hcs hf hrep hrax => ⟨?_, ?_, hrax⟩
  · refine hc1.called hL hrd hwr hcs hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [fST, fKS, by rw [hsp]; exact fB]
  · intro msg h hq'
    rw [← hm]; exact hrep msg (by rw [hm]; exact h) hq'

theorem kpad_mv(hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {pos : Arg} (h3 : argOk pos) {q : Nat}
    (hq : argVal t pos = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, .imm 0x1f,
      .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t fun t1 => Ctx L g m₀ t1 ∧ PadArgs t1 L.ST L.KS 136 q ∧
      Covers ([] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) ∧ Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr := by
  obtain ⟨fs, ks, kk, fST, fKS, fB, cv⟩ := sponge_facts hL
  rw [show [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, .imm 0x1f,
      .scr (Layout.oStream + 200)] = [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos),
      (.rcx, .imm 0x1f), (.r8, .scr (Layout.oStream + 200))] from rfl]
  refine (movs_ok _ t (fun q' hq' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, by decide, by show _ < _; rw [oStream_eq]; omega⟩
      · exact ⟨by decide, by decide, by decide, by show _ < _; omega⟩
      · exact ⟨by simp, by simp, by simp, h3⟩
      · exact ⟨by decide, by decide, by decide, by show _ < _; omega⟩
      · exact ⟨by decide, by decide, by decide, by show _ < _; rw [oStream_eq]; omega⟩)
    (by show List.Nodup [Reg.rdi, .rsi, .rdx, .rcx, .r8]; decide) hc.frIn fun t1 hv ho hm hr hw => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.moved (fun r h => ho r (callee_saved_args5 r h)) hm hr hw
  obtain ⟨v1, v2, v3, v4, v5⟩ := argsIn5 hv
  have hsp : t1.gpr .rsp = L.SP := hc1.rsp
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨by rw [v1]; simp only [argVal, hc.rbx], by rw [v2]; rfl,
      by rw [v3, hq], by rw [v5]; simp only [argVal, hc.rbx], by decide, hql, fs,
      by rw [hsp]; exact ks, by rw [hsp]; exact kk⟩
  have hcov : Covers ([] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) := by
    rw [hc1.regsIn, List.nil_append]
    exact Covers.trans cv (covers_frs L)
  have hcovw : Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr := by rw [hc1.wr]; exact cv
  exact ⟨hc1, ha, hcov, hcovw⟩

theorem kpad_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {pos : Arg} (h3 : argOk pos) {q : Nat}
    (hq : argVal t pos = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad pos) t fun t' => Ctx L g m₀ t' ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  obtain ⟨fs, ks, kk, fST, fKS, fB, cv⟩ := sponge_facts hL
  unfold kpad callA
  rw [show [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, .imm 0x1f,
      .scr (Layout.oStream + 200)] = [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos),
      (.rcx, .imm 0x1f), (.r8, .scr (Layout.oStream + 200))] from rfl]
  refine WP.seq (movs_ok _ t (fun q' hq' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, by decide, by show _ < _; rw [oStream_eq]; omega⟩
      · exact ⟨by decide, by decide, by decide, by show _ < _; omega⟩
      · exact ⟨by simp, by simp, by simp, h3⟩
      · exact ⟨by decide, by decide, by decide, by show _ < _; omega⟩
      · exact ⟨by decide, by decide, by decide, by show _ < _; rw [oStream_eq]; omega⟩)
    (by show List.Nodup [Reg.rdi, .rsi, .rdx, .rcx, .r8]; decide) hc.frIn fun t1 hv ho hm hr hw => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.moved (fun r h => ho r (callee_saved_args5 r h)) hm hr hw
  obtain ⟨v1, v2, v3, v4, v5⟩ := argsIn5 hv
  have hsp : t1.gpr .rsp = L.SP := hc1.rsp
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨by rw [v1]; simp only [argVal, hc.rbx], by rw [v2]; rfl,
      by rw [v3, hq], by rw [v5]; simp only [argVal, hc.rbx], by decide, hql, fs,
      by rw [hsp]; exact ks, by rw [hsp]; exact kk⟩
  have hcov : Covers ([] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) := by
    rw [hc1.regsIn, List.nil_append]
    exact Covers.trans cv (covers_frs L)
  have hcovw : Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr := by rw [hc1.wr]; exact cv
  refine pad_call ha hcov hcovw fun s' hrd hwr hcs hf hst => ⟨?_, fun msg h hq' => ?_⟩
  · refine hc1.called hL hrd hwr hcs hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [fST, fKS, by rw [hsp]; exact fB]
  · rw [hst msg (by rw [hm]; exact h) hq', v4]
    rfl

theorem ksqz_mv(hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o m : Nat} (ho1 : 12640 ≤ o) (ho2 : o + m ≤ Layout.oStream)
    (hm136 : m ≤ 136) :
    WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, .imm 0, .scr o, .imm m,
      .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t fun t1 => Ctx L g m₀ t1 ∧
      SqueezeArgs t1 L.ST (at' L.S o) L.KS 136 0 m ∧
      Covers ([] ++ [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) ∧
      Covers [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩] t1.wr := by
  obtain ⟨fs, ks, kk, fST, fKS, fB, cv⟩ := sponge_facts hL
  have hst := hL.st16
  rw [show [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, .imm 0, .scr o, .imm m,
      .scr (Layout.oStream + 200)] = [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, .imm 0), (.rcx, .scr o),
      (.r8, .imm m), (.r9, .scr (Layout.oStream + 200))] from rfl]
  refine (movs_ok _ t (args_ok6 _ _ _ _ _ _ (by show _ < _; rw [oStream_eq]; omega) (by show _ < _; omega)
    (by show _ < _; omega) (by show _ < _; rw [oStream_eq] at ho2; omega) (by show _ < _; omega)
    (by show _ < _; rw [oStream_eq]; omega)) (by show List.Nodup [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9]; decide) hc.frIn fun t1 hv ho hm hr hw => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.moved (fun r h => ho r (callee_saved_args r h)) hm hr hw
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := argsIn6 hv
  have hsp : t1.gpr .rsp = L.SP := hc1.rsp
  rw [oStream_eq] at ho2
  have hb : Region.Sub (below L.SP 16) L.CS := by rw [below_SP (by omega)]; exact Offset.sub_base _ (by omega)
  have ha : SqueezeArgs t1 L.ST (at' L.S o) L.KS 136 0 m :=
    ⟨by rw [v1]; simp only [argVal, hc.rbx], by rw [v2]; rfl,
      by rw [v3]; rfl, by rw [v4]; simp only [argVal, hc.rbx], by rw [v5]; rfl,
      by rw [v6]; simp only [argVal, hc.rbx], by decide, by decide, by omega,
      Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega) (by omega), fs,
      Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by omega) (by rw [oStream_eq]; omega),
      by rw [hsp]; exact ks, by rw [hsp]; exact (hL.cs_scr.sub_left hb).sub_right (hL.scr_sub (by omega)),
      by rw [hsp]; exact kk⟩
  have hcov : Covers [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩] [L.FR, L.SCR] := by
    refine Covers.of_sub fun r hr => ⟨L.SCR, by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Layout.oStream, rfl, by rw [oStream_eq]; simp⟩
    · exact ⟨o, rfl, by simp; omega⟩
    · exact ⟨Layout.oStream + 200, rfl, by rw [oStream_eq]; simp⟩
  have hcov' : Covers ([] ++ [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) := by
    rw [List.nil_append, hc1.regsIn]; exact Covers.trans hcov (covers_frs L)
  have hcovw : Covers [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩] t1.wr := by rw [hc1.wr]; exact hcov
  exact ⟨hc1, ha, hcov', hcovw⟩

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {o m : Nat} (ho1 : 12640 ≤ o) (ho2 : o + m ≤ Layout.oStream)
    (hm136 : m ≤ 136) :
    WP isa (ksqz (.scr o) m) t fun t' => Ctx L g m₀ t' ∧
      bytesAt t'.mem (at' L.S o) m = squeezeFrom 136 (stateAt t.mem L.ST) 0 m := by
  obtain ⟨fs, ks, kk, fST, fKS, fB, cv⟩ := sponge_facts hL
  have hst := hL.st16
  unfold ksqz callA
  rw [show [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, .imm 0, .scr o, .imm m,
      .scr (Layout.oStream + 200)] = [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, .imm 0), (.rcx, .scr o),
      (.r8, .imm m), (.r9, .scr (Layout.oStream + 200))] from rfl]
  refine WP.seq (movs_ok _ t (args_ok6 _ _ _ _ _ _ (by show _ < _; rw [oStream_eq]; omega) (by show _ < _; omega)
    (by show _ < _; omega) (by show _ < _; rw [oStream_eq] at ho2; omega) (by show _ < _; omega)
    (by show _ < _; rw [oStream_eq]; omega)) (by show List.Nodup [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9]; decide) hc.frIn fun t1 hv ho hm hr hw => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.moved (fun r h => ho r (callee_saved_args r h)) hm hr hw
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := argsIn6 hv
  have hsp : t1.gpr .rsp = L.SP := hc1.rsp
  rw [oStream_eq] at ho2
  have hb : Region.Sub (below L.SP 16) L.CS := by rw [below_SP (by omega)]; exact Offset.sub_base _ (by omega)
  have ha : SqueezeArgs t1 L.ST (at' L.S o) L.KS 136 0 m :=
    ⟨by rw [v1]; simp only [argVal, hc.rbx], by rw [v2]; rfl,
      by rw [v3]; rfl, by rw [v4]; simp only [argVal, hc.rbx], by rw [v5]; rfl,
      by rw [v6]; simp only [argVal, hc.rbx], by decide, by decide, by omega,
      Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega) (by omega), fs,
      Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by omega) (by rw [oStream_eq]; omega),
      by rw [hsp]; exact ks, by rw [hsp]; exact (hL.cs_scr.sub_left hb).sub_right (hL.scr_sub (by omega)),
      by rw [hsp]; exact kk⟩
  have hcov : Covers [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩] [L.FR, L.SCR] := by
    refine Covers.of_sub fun r hr => ⟨L.SCR, by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Layout.oStream, rfl, by rw [oStream_eq]; simp⟩
    · exact ⟨o, rfl, by simp; omega⟩
    · exact ⟨Layout.oStream + 200, rfl, by rw [oStream_eq]; simp⟩
  have hcov' : Covers ([] ++ [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) := by
    rw [List.nil_append, hc1.regsIn]; exact Covers.trans hcov (covers_frs L)
  have hcovw : Covers [⟨L.ST, 200⟩, ⟨at' L.S o, m⟩, ⟨L.KS, 640⟩] t1.wr := by rw [hc1.wr]; exact hcov
  refine squeeze_call ha hcov' hcovw fun s' hrd hwr hcs hf hout => ⟨?_, by rw [hout, hm]⟩
  refine hc1.called hL hrd hwr hcs hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [fST, free_hi hL ho1 (by omega), fKS, by rw [hsp]; exact fB]

/-! ## `H_msg` -/

theorem contains_prefix {a : Addr} {n k : Nat} (h : n ≤ k) : Region.Contains ⟨a, k⟩ a n := by
  simp [Region.Contains, h]

theorem sub_prefix' {a : Addr} {n k : Nat} (h : n ≤ k) : Region.Sub ⟨a, n⟩ ⟨a, k⟩ := Region.sub_prefix h

/-- What `kabs_ok` needs of an input buffer's first bytes. -/
theorem input_src (hL : L.Ok) {R : Region} (hR : R ∈ L.rd) (sR : L.SCR.Disjoint R) (kR : L.STK.Disjoint R) {N : Nat}
    (hN : N ≤ R.len) :
    InRegions (L.rd ++ [L.FR, L.SCR]) R.base N ∧ Region.Disjoint ⟨R.base, N⟩ ⟨L.ST, 840⟩ ∧
      (below L.SP 16).Disjoint ⟨R.base, N⟩ := by
  have hst := hL.st16
  have hb : Region.Sub (below L.SP 16) L.STK := by rw [below_SP (by omega)]; exact Offset.sub_base _ (by omega)
  refine ⟨⟨R, List.mem_append_left _ hR, contains_prefix hN⟩, ?_, ?_⟩
  · exact (sR.symm.sub_left (sub_prefix' hN)).sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  · exact (kR.sub_left hb).sub_right (sub_prefix' hN)

/-- What `kabs_ok` needs of a part of `scratch` below the state. -/
theorem scr_src (hL : L.Ok) {o N : Nat} (h : o + N ≤ Layout.oStream) :
    InRegions (L.rd ++ [L.FR, L.SCR]) (at' L.S o) N ∧ Region.Disjoint ⟨at' L.S o, N⟩ ⟨L.ST, 840⟩ ∧
      (below L.SP 16).Disjoint ⟨at' L.S o, N⟩ := by
  have hst := hL.st16
  rw [oStream_eq] at h
  have hb : Region.Sub (below L.SP 16) L.CS := by rw [below_SP (by omega)]; exact Offset.sub_base _ (by omega)
  refine ⟨⟨L.SCR, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
    Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by omega) (by rw [oStream_eq]; omega),
    (hL.cs_scr.sub_left hb).sub_right (hL.scr_sub (by omega))⟩

/-- `M′` and what precedes it in `H_msg`'s input, from the memory on entry. -/
def hIn (L : VL) (m₀ : Mem) : List Byte :=
  bytesAt m₀ L.sig L.n ++ bytesAt m₀ L.pk L.n ++ bytesAt m₀ (L.pk + BitVec.ofNat 64 L.n) L.n ++
    [0, BitVec.ofNat 8 L.ctxLen.toNat] ++ bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat

private theorem zeroState_eq : zeroState = .mov32 .rax (.imm 0) :: Impl.MlDsa.X86_64.Sign.zeroSt .rbx Layout.oStream := rfl

/-- What `kabs_ok` needs of the formatted message's two bytes. -/
theorem sp_src (hL : L.Ok) :
    InRegions (L.rd ++ [L.FR, L.SCR]) L.SP 2 ∧ Region.Disjoint ⟨L.SP, 2⟩ ⟨L.ST, 840⟩ ∧
      (below L.SP 16).Disjoint ⟨L.SP, 2⟩ := by
  have hst := hL.st16
  have hnB := hL.nB
  refine ⟨⟨L.FR, by simp, contains_prefix (by omega)⟩, ?_, ?_⟩
  · have := (hL.fr_scr (d := 0) (n := 2) (by omega)).sub_right (hL.scr_sub (o := Layout.oStream) (l := 840)
      (by rw [oStream_eq]; omega))
    simpa using this
  · rw [below_SP (by omega)]
    exact Offset.disjoint L.B (by omega) (by omega) (by omega)

theorem zero_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block zeroState) t fun t' => Ctx L g m₀ t' ∧ Repr t'.mem L.ST 136 [] := by
  rw [zeroState_eq]
  refine wp_mov32i fun t0 u0 => ?_
  have hb0 : t0.gpr .rbx = L.S := by rw [u0.other _ (by decide), hc.rbx]
  have hc0 : Ctx L g m₀ t0 := hc.regs u0.rd u0.wr u0.mem fun r hr => u0.other r (by
    intro e; subst e; revert hr; decide)
  refine WP.mono (Proof.MlDsa.X86_64.Sign.zeroSt_ok .rbx Layout.oStream t0 (by rw [u0.gpr]; rfl) fun i hi => ?_)
    fun t1 ⟨hz, hf, hk⟩ => ?_
  · rw [hb0, hc0.wr]
    show InRegions _ (at' L.S Layout.oStream + BitVec.ofNat 64 (8 * i)) 8
    rw [Levels.at_add]
    exact Levels.in_scr (by simp) (by rw [oStream_eq]; omega)
  · rw [hb0] at hz hf
    refine ⟨hc0.of_frame hL hk.2.1 hk.2.2 (hk.gpr (by simp)) (hk.gpr (by simp)) (fun r _ _ _ => hk.gpr (by simp)) hf
      fun r hr => ?_, Proof.MlKem.repr_nil hz⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact free_hi hL (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega)

/-- `hashM'` after the three strings: the formatted message, padding and squeezing. -/
theorem hash_tail {p : Params} (hL : L.Ok) (hm : p.m ≤ 64) {t4 : State} (hc4 : Ctx L g m₀ t4) {X : List Byte}
    (hR4 : Repr t4.mem L.ST 136 X) (hX : X.length = 3 * L.n) :
    WP isa (.seq (kabs .sp (.imm 2) (.imm (L.n * (0 + 1 + 1 + 1))))
      (.seq (kabs (.slot fCtx) (.slot fCtxLen) .ret)
        (.seq (kabs (.slot fMsg) (.slot fLen) .ret) (.seq (kpad .ret) (ksqz (.scr Layout.oDigest) p.m))))) t4
      fun t' => Ctx L g m₀ t' ∧ bytesAt t'.mem (at' L.S Layout.oDigest) p.m = Spec.Sha3.shake256
        (X ++ [0, BitVec.ofNat 8 L.ctxLen.toNat] ++ bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat) p.m := by
  have hn32 := hL.n32
  have ctxLt := hL.ctxLt
  have lenB : ∀ (m : Mem) (a : Addr) (k : Nat), (bytesAt m a k).length = k := Proof.MlKem.bytesAt_length
  -- `0 ‖ ctx_len`
  obtain ⟨i4, d4, k4⟩ := sp_src hL
  refine WP.seq (WP.mono (kabs_ok hL hc4 (src := .sp) (len := .imm 2)
    (pos := .imm (L.n * (0 + 1 + 1 + 1))) trivial (by show 2 < 2 ^ 32; omega)
    (by show _ < 2 ^ 32; omega) (by simp only [argVal, hc4.rsp]) rfl rfl (by omega) (by omega)
    i4 d4 k4) fun t5 ⟨hc5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by rw [hX]; omega)
  rw [hc4.hdr] at hR5
  -- `ctx`
  obtain ⟨i5, d5, k5⟩ := input_src hL (R := L.CTX) (by simp) hL.sCtx hL.kCtx (N := L.ctxLen.toNat) (Nat.le_refl _)
  generalize hq5 : (L.n * (0 + 1 + 1 + 1) + 2) % 136 = q5 at hx5
  refine WP.seq (WP.mono (kabs_ok hL hc5 (src := .slot fCtx) (len := .slot fCtxLen) (pos := .ret)
    (N := L.ctxLen.toNat) (q := q5)
    (by show 40 + 8 ≤ 72; omega) (by show 32 + 8 ≤ 72; omega) trivial
    (by simp only [argVal, fCtx, hc5.rsp]; exact hc5.pCtx)
    (by simp only [argVal, fCtxLen, hc5.rsp]; rw [hc5.pCtxLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by simp only [argVal]; rw [← hx5, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)
    (by have := L.ctxLen.isLt; omega) i5 d5 k5) fun t6 ⟨hc6, hR6, hx6⟩ => ?_)
  have hR6 := hR6 _ hR5 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  rw [hc5.bytesAt_eq hL.sCtx hL.kCtx (by have := L.ctxLen.isLt; omega)] at hR6
  -- the message
  obtain ⟨i6, d6, k6⟩ := input_src hL (R := L.MSG) (by simp) hL.sMsg hL.kMsg (N := L.len.toNat) (Nat.le_refl _)
  generalize hq6 : (q5 + L.ctxLen.toNat) % 136 = q6 at hx6
  refine WP.seq (WP.mono (kabs_ok hL hc6 (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
    (N := L.len.toNat) (q := q6)
    (by show 56 + 8 ≤ 72; omega) (by show 48 + 8 ≤ 72; omega) trivial
    (by simp only [argVal, fMsg, hc6.rsp]; exact hc6.pMsg)
    (by simp only [argVal, fLen, hc6.rsp]; rw [hc6.pLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by simp only [argVal]; rw [← hx6, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)
    (by have := L.len.isLt; omega) i6 d6 k6) fun t7 ⟨hc7, hR7, hx7⟩ => ?_)
  have hR7 := hR7 _ hR6 (by simp only [List.length_append, lenB, List.length_cons, List.length_nil]; omega)
  rw [hc6.bytesAt_eq hL.sMsg hL.kMsg (by have := L.len.isLt; omega)] at hR7
  -- pad and squeeze
  generalize hq7 : (q6 + L.len.toNat) % 136 = q7 at hx7
  refine WP.seq (WP.mono (kpad_ok hL hc7 (pos := .ret) (q := q7) trivial
    (by simp only [argVal]; rw [← hx7, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)) fun t8 ⟨hc8, hS8⟩ => ?_)
  have hS8 := hS8 _ hR7 (by simp only [List.length_append, lenB, List.length_cons, List.length_nil]; omega)
  have eD : Layout.oDigest = 30304 := rfl
  have hd1 : 12640 ≤ Layout.oDigest := by rw [eD]; omega
  have hd2 : Layout.oDigest + p.m ≤ Layout.oStream := by rw [eD, oStream_eq]; omega
  refine WP.mono (ksqz_ok hL hc8 (o := Layout.oDigest) (m := p.m) hd1 hd2 (by omega))
    fun t9 ⟨hc9, hd⟩ => ⟨hc9, ?_⟩
  rw [hd, hS8, Proof.MlKem.shake256_eq]

theorem hash_ok {p : Params} (hL : L.Ok) (hn : L.n = p.n) (hsl : L.n ≤ L.sigL) (hm : p.m ≤ 64) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (hashM' p [.slot Impl.SlhDsa.X86_64.Verify.fVSig, .scr Layout.oPkSeed, .scr Layout.oPkRoot]
      (.scr Layout.oDigest) p.m) t fun t' => Ctx L g m₀ t' ∧
        bytesAt t'.mem (at' L.S Layout.oDigest) p.m = Spec.Sha3.shake256 (hIn L m₀) p.m := by
  have hn32 := hL.n32
  have ctxLt := hL.ctxLt
  have eP : Layout.oPkSeed = 3232 := rfl
  have eR : Layout.oPkRoot = 3264 := rfl
  have lenB : ∀ (m : Mem) (a : Addr) (k : Nat), (bytesAt m a k).length = k := Proof.MlKem.bytesAt_length
  unfold hashM'
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldr_cons, List.foldr_nil, List.length_cons, List.length_nil]
  rw [← hn]
  refine WP.seq (WP.mono (zero_ok hL hc) fun t1 ⟨hc1, hR1⟩ => ?_)
  -- `R`
  obtain ⟨i1, d1, k1⟩ := input_src hL (R := L.SIG) (by simp) hL.sSig hL.kSig (N := L.n) hsl
  refine WP.seq (WP.mono (kabs_ok hL hc1 (src := .slot Impl.SlhDsa.X86_64.Verify.fVSig) (len := .imm L.n)
    (pos := .imm (L.n * 0)) (by show 16 + 8 ≤ 72; omega) (by show L.n < 2 ^ 32; omega) (by show _ < 2 ^ 32; omega)
    (by simp only [argVal, Impl.SlhDsa.X86_64.Verify.fVSig, hc1.rsp]; exact hc1.pSig) rfl rfl (by omega) (by omega)
    i1 d1 k1) fun t2 ⟨hc2, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 (by simp)
  rw [hc1.bytesAt_eq (hL.sSig.sub_right (sub_prefix' hsl)) (hL.kSig.sub_right (sub_prefix' hsl)) (by omega)] at hR2
  -- `PK.seed`
  obtain ⟨i2, d2, k2⟩ := scr_src hL (o := Layout.oPkSeed) (N := L.n) (by rw [eP, oStream_eq]; omega)
  refine WP.seq (WP.mono (kabs_ok hL hc2 (src := .scr Layout.oPkSeed) (len := .imm L.n)
    (pos := .imm (L.n * (0 + 1))) (by show _ < 2 ^ 31; rw [eP]; omega) (by show L.n < 2 ^ 32; omega)
    (by show _ < 2 ^ 32; omega) (by simp only [argVal, hc2.rbx]) rfl rfl (by omega) (by omega)
    i2 d2 k2) fun t3 ⟨hc3, hR3, _⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp [lenB]; omega)
  rw [hc2.kSeed] at hR3
  -- `PK.root`
  obtain ⟨i3, d3, k3⟩ := scr_src hL (o := Layout.oPkRoot) (N := L.n) (by rw [eR, oStream_eq]; omega)
  refine WP.seq (WP.mono (kabs_ok hL hc3 (src := .scr Layout.oPkRoot) (len := .imm L.n)
    (pos := .imm (L.n * (0 + 1 + 1))) (by show _ < 2 ^ 31; rw [eR]; omega) (by show L.n < 2 ^ 32; omega)
    (by show _ < 2 ^ 32; omega) (by simp only [argVal, hc3.rbx]) rfl rfl (by omega) (by omega)
    i3 d3 k3) fun t4 ⟨hc4, hR4, _⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp [lenB]; omega)
  rw [hc3.kRoot] at hR4
  refine WP.mono (hash_tail hL hm hc4 hR4 (by simp only [List.nil_append, List.length_append, lenB]; omega))
    fun t' ⟨hc', hd⟩ => ⟨hc', by rw [hd]; simp only [hIn, List.nil_append]⟩

end VG.Proof.SlhDsa.X86_64.VerifyTop
