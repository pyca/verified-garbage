module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.RsaPss.EncodingContract

/-!
# RSASSA-PSS signing on x86-64, around the encoding: the call of `encode`

`encArgs` writes a zero byte at `scratch + oEm`, and `encode`'s arguments:
`em = scratch + oEm + lo` (`emLen` bytes), the digest, the salt, `emBits`, and
the working space from `scratch + oEnc` (`encArgs_ok`); `encode` then runs
under its contract (`enc_pre`) and returns with the encoding at `em` if it
fits, the frame and the rest of our working space kept (`enc_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {G : Spec.Mgf1.Hash}

/-! ## The arguments -/

def encA1 : List Instr := scr .rdi oEm ++ [.mov32 .rax (.imm 0), .store8 (at_ .rdi) .rax]

def encA2 : List Instr :=
  ([.alu .add .rdi (.mem (sp sLo)), .mov .rsi (.mem (sp sEml)), .mov .rdx (.mem (sp sDig)),
    .mov .rcx (.mem (sp sSalt)), .mov .r8 (.mem (sp sSaltLen)), .mov .r9 (.mem (sp sBits))] : List Instr) ++
  scr .rax oEnc ++ [.store (sp 0) .rax]

def encA3 : List Instr :=
  [.mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm (BitVec.ofNat 32 (oEnc / 8))), .store (sp 8) .rax]

theorem encArgs_eq : encArgs = encA1 ++ encA2 ++ encA3 := rfl

theorem encArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo eb el : Nat} {dig q sl sw : BitVec 64}
    (h22 : W 22 = sw) (h26 : W 26 = BitVec.ofNat 64 lo) (h27 : W 27 = BitVec.ofNat 64 eb)
    (h28 : W 28 = BitVec.ofNat 64 el) (h37 : W 37 = dig) (h39 : W 39 = q) (h40 : W 40 = sl) :
    WP isa (.block encArgs) u fun u' => Lay u' F S ∧ Keep [.rdi, .rax, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Rep u'.mem F S (upd V oEm 0) (upd (upd W 0 (off S oEnc)) 1 (sw - BitVec.ofNat 64 (oEnc / 8))) ∧
      u'.gpr .rdi = off S (oEm + lo) ∧ u'.gpr .rsi = BitVec.ofNat 64 el ∧ u'.gpr .rdx = dig ∧ u'.gpr .rcx = q ∧
      u'.gpr .r8 = sl ∧ u'.gpr .r9 = BitVec.ofNat 64 eb := by
  have G' := L.geo
  have hs := L.slot
  simp only [Bignum.word] at hs
  have R1 := R.wb G' (o := oEm) (by decide) 0
  have R2 := R1.wf G' (k := 0) (by decide) (off S oEnc)
  have R3 := R2.wf G' (k := 1) (by decide) (sw - BitVec.ofNat 64 (oEnc / 8))
  rw [show off F (8 * 0) = F from BitVec.add_zero F] at R2 R3
  rw [show off F (8 * 1) = off F 8 from rfl] at R3
  rw [encArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun v => v.mem = u.mem.writeW (off S oEm) (0 : Byte) ∧
      v.gpr .rdi = off S oEm) ?_ rfl) fun v ⟨⟨hm1, hdi1⟩, k1⟩ => ?_
  · xrun [encA1, scr, List.cons_append, List.nil_append, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), L.sst8 (d := oEm) (by decide),
      show BitVec.setWidth 8 (BitVec.setWidth 64 (0 : BitVec 32)) = (0 : Byte) from rfl]
  have L1 : Lay v F S := L.of_rep R (hm1 ▸ R1) (k1.gpr (by decide)) k1.2.2
  have R1' : Rep v.mem F S (upd V oEm 0) W := hm1 ▸ R1
  have hs1 := L1.slot
  simp only [Bignum.word] at hs1
  have hst0 : InRegions v.wr F 8 := by
    have := L1.st (d := 0) (by decide); rwa [off, BitVec.add_zero] at this
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax] (Q := fun w =>
      w.mem = v.mem.writeW F (off S oEnc) ∧ w.gpr .rdi = off S (oEm + lo) ∧ w.gpr .rsi = BitVec.ofNat 64 el ∧
      w.gpr .rdx = dig ∧ w.gpr .rcx = q ∧ w.gpr .r8 = sl ∧ w.gpr .r9 = BitVec.ofNat 64 eb) ?_ rfl)
    fun w ⟨⟨hm2, hdi, hsi, hdx, hcx, h8, h9⟩, k2⟩ => ?_
  · xrun [encA2, scr, List.cons_append, List.nil_append, ea_sp, L1.rsp, L1.ld (d := sScr) (by decide),
      L1.ld (d := sLo) (by decide), L1.ld (d := sEml) (by decide), L1.ld (d := sDig) (by decide),
      L1.ld (d := sSalt) (by decide), L1.ld (d := sSaltLen) (by decide), L1.ld (d := sBits) (by decide),
      hst0, hs1, hdi1, R1'.rd (d := sLo) 26 rfl (by decide), R1'.rd (d := sEml) 28 rfl (by decide),
      R1'.rd (d := sDig) 37 rfl (by decide), R1'.rd (d := sSalt) 39 rfl (by decide),
      R1'.rd (d := sSaltLen) 40 rfl (by decide), R1'.rd (d := sBits) 27 rfl (by decide), h26, h27, h28, h37, h39,
      h40, VG.Proof.MlKem.X86_64.sx_ofNat (show oEnc < 2 ^ 31 by decide), off_plus]
  have R2' : Rep w.mem F S (upd V oEm 0) (upd W 0 (off S oEnc)) := by rw [hm2, hm1]; exact R2
  have L2 : Lay w F S := L1.of_rep' R1' R2' rfl (k2.gpr (by decide)) k2.2.2
  refine WP.mono (WP.keep [.rax] (Q := fun y => y.mem = w.mem.writeW (off F 8) (sw - BitVec.ofNat 64 (oEnc / 8)))
    ?_ rfl) fun y ⟨hm3, k3⟩ => ?_
  · xrun [encA3, ea_sp, L2.rsp, L2.ld (d := sScrLen) (by decide), L2.st (d := 8) (by decide),
      R2'.rd (d := sScrLen) 22 rfl (by decide), h22, VG.Proof.MlKem.X86_64.sx_ofNat (show oEnc / 8 < 2 ^ 31 by decide)]
    simp [upd, h22]
  have R3' : Rep y.mem F S (upd V oEm 0) (upd (upd W 0 (off S oEnc)) 1 (sw - BitVec.ofNat 64 (oEnc / 8))) := by
    rw [hm3, hm2, hm1]; exact R3
  refine ⟨L2.of_rep' R2' R3' rfl (k3.gpr (by decide)) k3.2.2, ((k1.trans k2).trans k3).mono (by decide),
    R3', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [k3.gpr (by decide)]; assumption)

/-! ## The call -/

variable (G) in
/-- What `encode` reads: the digest, the salt and its stack arguments. -/
def eRd (s : State) : List Region :=
  [⟨stackArg s 10, G.len⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨fb s, 16⟩]

/-- What it writes: the encoding's place, and its working space. -/
def eWr (s : State) (lo el : Nat) : List Region :=
  [⟨off (stackArg s 13) (oEm + lo), el⟩,
    ⟨off (stackArg s 13) oEnc, (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩]

theorem enc_pre {s t : State} (hp : SPre G s) (hsp : t.gpr .rsp = fb s) {lo eb el : Nat}
    (h0 : word t.mem (fb s) (8 * 0) = off (stackArg s 13) oEnc)
    (h1 : word t.mem (fb s) (8 * 1) = stackArg s 14 - BitVec.ofNat 64 (oEnc / 8))
    (hdi : t.gpr .rdi = off (stackArg s 13) (oEm + lo)) (hsi : t.gpr .rsi = BitVec.ofNat 64 el)
    (hdx : t.gpr .rdx = stackArg s 10) (hcx : t.gpr .rcx = stackArg s 11) (h8 : t.gpr .r8 = stackArg s 12)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 eb) (hlo : lo ≤ 1) (heb1 : 1 ≤ eb) (heb2 : eb ≤ Proof.RsaPss.maxEmBits)
    (hel : el = Spec.RsaPss.emLength eb) :
    (encK G).pre (t.callEntry.withRegions (eRd G s) (eWr s lo el)) := by
  have hE0 := (stackArg_call hp hsp (eRd G s) (eWr s lo el) (i := 0) (by decide)).trans h0
  have hE1 := (stackArg_call hp hsp (eRd G s) (eWr s lo el) (i := 1) (by decide)).trans h1
  have hel2 : el ≤ 1024 := by rw [hel]; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega
  simp only [encK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hsp, stackArgAddr_call hsp, hE0, hE1]
  have hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  have h8' := fb_sub8' hp
  have hsc : (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 14).toNat - 512 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 (oEnc / 8)).toNat = 512 from rfl]; omega_using [hsl]
  have toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]
  have hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega
  have heb' : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega
  rw [hel', heb']
  -- What lies in what.
  have sI : Region.Sub ⟨off (stackArg s 13) (oEm + lo), el⟩ ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_using [hsl, c1, hlo, hel2])
  have sR : Region.Sub ⟨off (stackArg s 13) oEnc, (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩
      ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c3])
  have sA : Region.Sub ⟨fb s, 16⟩ (stkR s) := fun a h => frame_sub s a (Region.sub_prefix (by decide) a h)
  have sRet : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := ret_sub s
  have sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 encStack, encStack⟩ (stkR s) := by
    simp only [stkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 16⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 16) (by omega_using [])).symm
  have dKA : (⟨fb s - 8 - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨fb s, 16⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 408) (k := 16) (by omega_using [])).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dIR : (⟨off (stackArg s 13) (oEm + lo), el⟩ : Region).Disjoint
      ⟨off (stackArg s 13) oEnc, (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega_using [hlo, hel2, c1, c3])) (by omega_using [hsl, c1, hlo, hel2])
      (by rw [hsc]; omega_using [wS, c3, hsl])
  have hsA : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨fb s, 16⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by unfold encStack; omega_arith, by omega_using [hF, h392, h8'], rfl, rfl,
    (hp.ddgs.sub_right sI).symm, (hp.dsas.sub_right sI).symm, dIR, hsA.sub_left sI,
    hp.ddgs.sub_right sR, hp.dsas.sub_right sR, hsA.sub_left sR,
    (hp.dKs.sub_left sRet).sub_right sI, hp.dKdg.sub_left sRet, hp.dKsa.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    (hp.dKs.sub_left sStk).sub_right sI, hp.dKdg.sub_left sStk, hp.dKsa.sub_left sStk,
    (hp.dKs.sub_left sStk).sub_right sR, dKA,
    by rw [toNat_off (by omega_using [hsl, wS, c1, hlo, hel2])]; omega_using [hsl, wS, c1, hlo, hel2],
    hp.wDg, hp.wSa, by rw [toNat_off (by omega_using [hsl, wS, c3]), hsc]; omega_using [hsl, wS, c3],
    heb1, heb2, hel, by rw [hsc]; unfold Proof.RsaPss.encodingScratchWords; have := hp.k1; omega_using [hsl, this]⟩

theorem enc_covers {s t : State} (hp : SPre G s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr) {lo el : Nat}
    (hlo : lo ≤ 1) (hel2 : el ≤ 1024) :
    Covers (eRd G s ++ eWr s lo el) (t.rd ++ t.wr) ∧ Covers (eWr s lo el) t.wr := by
  have hsl := hp.hsl
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  have hsc : (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 14).toNat - 512 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 (oEnc / 8)).toNat = 512 from rfl]; omega_using [hsl]
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (eWr s lo el) t.wr := Covers.of_sub fun r hr => by
    simp only [eWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hscr, oEm + lo, rfl, by dsimp only; omega_using [hsl, c1, hlo, hel2]⟩
    · exact ⟨_, hscr, oEnc, rfl, by dsimp only; rw [hsc]; omega_using [hsl, c3]⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  simp only [eRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩

/-- `Rep` after a call that writes, of the frame and our working space, only
the ranges `rgs` of the latter. -/
theorem Rep.of_call {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G' : Geo F S)
    (R : Rep m F S V W) {rgs : List (Nat × Nat)}
    (hF : ∀ x, (∀ p ∈ rgs, ¬ (⟨off S p.1, p.2⟩ : Region).Contains x 1) →
      ((⟨S, oRsa⟩ : Region).Contains x 1 ∨ (⟨F, frameBytes⟩ : Region).Contains x 1) → m' x = m x)
    (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa) :
    Rep m' F S (fun o => if inR rgs o then m' (off S o) else V o) W where
  scr o ho := by
    split
    · rfl
    · rename_i hn
      rw [hF _ (fun p hp hc => hn ⟨p, hp, ?_⟩) (.inl (cS S (o := o) (n := 1) (by omega) |>.byte
        (by rw [BitVec.sub_self]; decide))), R.scr o ho]
      have := hrg p hp
      have := (Offset.lt_iff (off S o) S (d := p.1) (n := p.2) (by have := G'.Sw; unfold oRsa at *; omega)).mp hc
      rwa [off, Mem.sub_ofNat_toNat S (by unfold oRsa at *; omega)] at this
  fr k hk := by
    rw [← R.fr k hk]
    refine Mem.readW_congr fun i hi => hF _ (fun p hp hc => ?_) (.inr ?_)
    · have := hrg p hp
      exact G'.dFS _ ((cF F hk).byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega))
        ((Offset.sub_base S (by omega) : Region.Sub ⟨off S p.1, p.2⟩ ⟨S, oRsa⟩) _ hc)
    · exact (cF F hk).byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)

theorem enc_call {encN : String} {encC : Prog isa}
    (hv : ∀ s, (encK G).pre s → ∃ t s', Exec isa encC s t s' ∧ abiPreserved s s' ∧ (encK G).post s s')
    (hspC : SpSafe encC) (hd : encC.x86_64Depth ≤ encStack)
    {s t : State} (hp : SPre G s) (hst : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    (hM : Frame (wrR s) s.mem t.mem) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem (fb s) (stackArg s 13) V W) {lo eb el : Nat}
    (h0 : word t.mem (fb s) (8 * 0) = off (stackArg s 13) oEnc)
    (h1 : word t.mem (fb s) (8 * 1) = stackArg s 14 - BitVec.ofNat 64 (oEnc / 8))
    (hdi : t.gpr .rdi = off (stackArg s 13) (oEm + lo)) (hsi : t.gpr .rsi = BitVec.ofNat 64 el)
    (hdx : t.gpr .rdx = stackArg s 10) (hcx : t.gpr .rcx = stackArg s 11) (h8 : t.gpr .r8 = stackArg s 12)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 eb) (hlo : lo ≤ 1) (heb1 : 1 ≤ eb) (heb2 : eb ≤ Proof.RsaPss.maxEmBits)
    (hel : el = Spec.RsaPss.emLength eb) :
    WP isa (.call encN encC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (wrR s) s.mem t'.mem ∧
      Rep t'.mem (fb s) (stackArg s 13)
        (fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then t'.mem (off (stackArg s 13) o) else V o) W ∧
      match Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
          (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) eb with
      | some e => (t'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.bytesAt t'.mem (off (stackArg s 13) (oEm + lo)) el = e
      | none => (t'.gpr .rax).setWidth 32 = 0 := by
  have hel2 : el ≤ 1024 := by rw [hel]; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega
  obtain ⟨hc, hw⟩ := enc_covers hp hrd hwr hlo hel2
  refine X86_64.WP.callF hv hspC (by unfold encStack at hd; omega)
    (enc_pre hp hst h0 h1 hdi hsi hdx hcx h8 h9 hlo heb1 heb2 hel) hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  have hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS; have hk1 := hp.k1
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc : (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 14).toNat - 512 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 (oEnc / 8)).toNat = 512 from rfl]; omega_using [hsl]
  rw [hst] at hf
  -- What the call writes, within what the function may write.
  have sI : Region.Sub ⟨off (stackArg s 13) (oEm + lo), el⟩ (scrR s) :=
    Offset.sub_base _ (by omega_using [hsl, c1, hlo, hel2])
  have sR : Region.Sub ⟨off (stackArg s 13) oEnc, (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ (scrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c3])
  have sBel : Region.Sub (below (fb s) (encC.x86_64Depth + 8)) (stkR s) := by
    simp only [below, fb, stkR, sub_sub']
    exact Offset.sub_below _ (by unfold encStack at hd; omega_using [hd, h392, hss])
      (by unfold encStack at hd; omega_using [hd, hss])
  have dFb : (frR s).Disjoint (below (fb s) (encC.x86_64Depth + 8)) :=
    Offset.base_disjoint_below (fb s) (by unfold encStack at hd; omega_using [hd, h392])
  have hS8 : Region.Sub ⟨stackArg s 13, oRsa⟩ (scrR s) := Region.sub_prefix (by omega_using [hsl, c2])
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), ?_, ?_⟩
  · simp only [eWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sI⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sR⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · refine R.of_call hp.geo (fun x hx hin => hf x fun r hr hc => ?_) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> dsimp only <;> omega_using [c1, c2, c3, hlo, hel2])
    simp only [eWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (List.mem_cons_self ..) hc
    · rcases hin with hin | hin
      · refine hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_
        have h1 := (Offset.lt_iff x (stackArg s 13) (d := oEnc) (n := (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8)
          (by rw [hsc]; omega_using [wS, c3, hsl])).mp (by simp only [Region.Contains, off] at hc; omega)
        have h2 : (x - stackArg s 13).toNat < oRsa := by simp only [Region.Contains] at hin; omega
        show (x - (stackArg s 13 + BitVec.ofNat 64 oEnc)).toNat + 1 ≤ oRsa - oEnc
        have := (Offset.lt_iff x (stackArg s 13) (d := oEnc) (n := oRsa - oEnc) (by omega_using [c2, c3])).mpr
          ⟨h1.1, by omega_using [h2, c2, c3]⟩
        omega
      · exact (hp.dKs.sub_left (frame_sub s)) x hin (sR x hc)
    · rcases hin with hin | hin
      · exact hp.dKs x (sBel x hc) (hS8 x hin)
      · exact dFb x hin hc
  · have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
    have b : ∀ {R : Region}, (stkR s).Disjoint R → (outR s).Disjoint R → R.Disjoint (scrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hO hS hl => bytesAt_frame fSE (in_apart hK hO hS) hl
    have hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega
    have heb' : (BitVec.ofNat 64 eb).toNat = eb := by
      rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega
    simp only [encK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hsi, hdx, hcx, h8, h9, hm₂, hg₂ .rax (by decide), hel', heb'] at hpost
    rw [b (R := ⟨stackArg s 10, G.len⟩) hp.dKdg hp.dOdg hp.ddgs (by have := hp.wDg; dsimp only; omega),
      b (R := ⟨stackArg s 11, (stackArg s 12).toNat⟩) hp.dKsa hp.dOsa hp.dsas
        (by have := hp.wSa; dsimp only; omega)] at hpost
    exact hpost

end VG.Proof.RsaPss.X86_64
