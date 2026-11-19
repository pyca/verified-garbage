module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.EncodingContract

/-! ### `RsaPss.X86_64.SignCCall`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64, around the encoding: the call of `encode`

`encArgs` writes a zero byte at `scratch + oEm`, and `encode`'s arguments:
`em = scratch + oEm + lo` (`emLen` bytes), the digest, the salt, `emBits`,
the working space from `scratch + oEnc`, and the tables (`encArgs_ok`);
`encode` then runs under its contract (`enc_pre`) and returns with the
encoding at `em` if it fits, the frame and the rest of our working space kept
(`enc_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {tsH tsG : List FnTable}

/-! ## The arguments -/

def encA1 : List Instr := scr .rdi oEm ++ [.mov32 .rax (.imm 0), .store8 (at_ .rdi) .rax]

def encA2 : List Instr :=
  ([.alu .add .rdi (.mem (sp sLo)), .mov .rsi (.mem (sp sEml)), .mov .rdx (.mem (sp sDig)),
    .mov .rcx (.mem (sp sSalt)), .mov .r8 (.mem (sp sSaltLen)), .mov .r9 (.mem (sp sBits))] : List Instr) ++
  scr .rax oEnc ++ [.store (sp 0) .rax]

def encA3 : List Instr :=
  [.mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm (BitVec.ofNat 32 (oEnc / 8))), .store (sp 8) .rax]

def encA4 : List Instr :=
  [.mov .rax (.mem (arg 16)), .store (sp 16) .rax, .mov .rax (.mem (arg 17)), .store (sp 24) .rax]

theorem encArgs_eq : encArgs = encA1 ++ encA2 ++ encA3 ++ encA4 := rfl

/-- The first three pieces of `encArgs`. -/
theorem encArgs3_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo eb el : Nat} {dig q sl sw : BitVec 64}
    (h22 : W 22 = sw) (h26 : W 26 = BitVec.ofNat 64 lo) (h27 : W 27 = BitVec.ofNat 64 eb)
    (h28 : W 28 = BitVec.ofNat 64 el) (h37 : W 37 = dig) (h39 : W 39 = q) (h40 : W 40 = sl) :
    WP isa (.block (encA1 ++ encA2 ++ encA3)) u fun u' => Lay u' F S ∧ Keep [.rdi, .rax, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Rep u'.mem F S (upd V oEm 0) (upd (upd W 0 (off S oEnc)) 1 (sw - BitVec.ofNat 64 (oEnc / 8))) ∧
      u'.gpr .rdi = off S (oEm + lo) ∧ u'.gpr .rsi = BitVec.ofNat 64 el ∧ u'.gpr .rdx = dig ∧ u'.gpr .rcx = q ∧
      u'.gpr .r8 = sl ∧ u'.gpr .r9 = BitVec.ofNat 64 eb := by
  have G' := L.geo
  have hs := L.slot
  simp only [Bignum.word] at hs
  obtain R1 := R.wb G' (o := oEm) (by decide) 0
  obtain R2 := R1.wf G' (k := 0) (by decide) (off S oEnc)
  obtain R3 := R2.wf G' (k := 1) (by decide) (sw - BitVec.ofNat 64 (oEnc / 8))
  rw [show off F (8 * 0) = F from BitVec.add_zero F] at R2 R3
  rw [show off F (8 * 1) = off F 8 from rfl] at R3
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun v => v.mem = u.mem.writeW (off S oEm) (0 : Byte) ∧
      v.gpr .rdi = off S oEm) ?_ rfl) fun v ⟨⟨hm1, hdi1⟩, k1⟩ => ?_
  · xrun [encA1, scr, List.cons_append, List.nil_append, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), L.sst8 (d := oEm) (by decide),
      show BitVec.setWidth 8 (BitVec.setWidth 64 (0 : BitVec 32)) = (0 : Byte) from rfl]
  obtain L1 : Lay v F S := L.of_rep R (hm1 ▸ R1) (k1.gpr (by decide)) k1.2.2
  obtain R1' : Rep v.mem F S (upd V oEm 0) W := hm1 ▸ R1
  have hs1 := L1.slot
  simp only [Bignum.word] at hs1
  obtain hst0 : InRegions v.wr F 8 := by
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
  obtain R2' : Rep w.mem F S (upd V oEm 0) (upd W 0 (off S oEnc)) := by rw [hm2, hm1]; exact R2
  obtain L2 : Lay w F S := L1.of_rep' R1' R2' rfl (k2.gpr (by decide)) k2.2.2
  refine WP.mono (WP.keep [.rax] (Q := fun y => y.mem = w.mem.writeW (off F 8) (sw - BitVec.ofNat 64 (oEnc / 8)))
    ?_ rfl) fun y ⟨hm3, k3⟩ => ?_
  · xrun [encA3, ea_sp, L2.rsp, L2.ld (d := sScrLen) (by decide), L2.st (d := 8) (by decide),
      R2'.rd (d := sScrLen) 22 rfl (by decide), h22, VG.Proof.MlKem.X86_64.sx_ofNat (show oEnc / 8 < 2 ^ 31 by decide)]
    simp [upd, h22]
  obtain R3' : Rep y.mem F S (upd V oEm 0) (upd (upd W 0 (off S oEnc)) 1 (sw - BitVec.ofNat 64 (oEnc / 8))) := by
    rw [hm3, hm2, hm1]; exact R3
  refine ⟨L2.of_rep' R2' R3' rfl (k3.gpr (by decide)) k3.2.2, ((k1.trans k2).trans k3).mono (by decide),
    R3', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [k3.gpr (by decide)]; assumption)

/-- The last piece: the tables to `encode`'s stack arguments 2 and 3. -/
theorem encA4_ok {s u : State} (hp : SPre tsH tsG s) {S : Addr} (L : Lay u (fb s) S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) (hrd : u.rd = s.rd) (hA : ArgsKept s u.mem) :
    WP isa (.block encA4) u fun u' => Lay u' (fb s) S ∧ Keep [.rax] u u' ∧
      Rep u'.mem (fb s) S V (upd (upd W 2 (stackArg s 16)) 3 (stackArg s 17)) := by
  obtain hF := fb_toNat hp
  have := hp.sp2
  have G' := L.geo
  obtain hin : ∀ j, j < 18 → InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := fun j hj => by
    rw [argAddr]; exact hp.argIn hrd (by omega_using [hj])
  obtain hv : ∀ j, j < 18 → u.mem.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := fun j hj => by
    rw [argAddr]; exact hA j hj
  obtain R1 := R.wf G' (k := 2) (by decide) (stackArg s 16)
  obtain R2 := R1.wf G' (k := 3) (by decide) (stackArg s 17)
  rw [show off (fb s) (8 * 2) = off (fb s) 16 from rfl] at R1 R2
  rw [show off (fb s) (8 * 3) = off (fb s) 24 from rfl] at R2
  obtain hv17 : (u.mem.writeW (off (fb s) 16) (stackArg s 16)).readW (off (fb s) (frameBytes + 8 + 8 * 17)) 64 =
      stackArg s 17 := by
    rw [argAddr]; exact (ArgsKept.write hp hA (d := 16) (by decide) _) 17 (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = (u.mem.writeW (off (fb s) 16) (stackArg s 16)).writeW
      (off (fb s) 24) (stackArg s 17)) ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [encA4, arg, ea_sp, L.rsp, hin 16 (by decide), hin 17 (by decide), hv 16 (by decide), hv17,
      L.st (d := 16) (by decide), L.st (d := 24) (by decide)]
  obtain R' : Rep u'.mem (fb s) S V (upd (upd W 2 (stackArg s 16)) 3 (stackArg s 17)) := by rw [hm]; exact R2
  exact ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, R'⟩

/-- A table's word, read from memory that changed only in the writable
regions and below the frame. -/
theorem tab_read {s : State} (hp : SPre tsH tsG s) {m : Mem} (hM : Frame (wrR s) s.mem m) {i o : Nat}
    (hi : i = 16 ∨ i = 17) (ho : o + 8 ≤ 56) :
    m.readW (off (stackArg s i) o) 64 = s.mem.readW (off (stackArg s i) o) 64 := by
  obtain hw : (stackArg s i).toNat + 56 ≤ 2 ^ 64 := by rcases hi with rfl | rfl <;> [have := hp.wTH; have := hp.wTG] <;> omega_using [this]
  refine hM.readW (r := ⟨stackArg s i, 56⟩) (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])) (fun r hr => ?_) (by decide)
  obtain sH : Region.Sub ⟨stackArg s 16, 56⟩ ⟨stackArg s 16, 88⟩ := Region.sub_prefix (by decide)
  obtain sG : Region.Sub ⟨stackArg s 17, 56⟩ ⟨stackArg s 17, 88⟩ := Region.sub_prefix (by decide)
  simp only [wrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hi with rfl | rfl <;> rcases hr with rfl | rfl | rfl
  · exact (hp.dKtH.sub_right sH).symm
  · exact (hp.dOtH.sub_right sH).symm
  · exact (hp.dstH.sub_right sH).symm
  · exact (hp.dKtG.sub_right sG).symm
  · exact (hp.dOtG.sub_right sG).symm
  · exact (hp.dstG.sub_right sG).symm

/-- The tables' words in a state whose memory changed only in the writable
regions and below the frame. -/
theorem TabsAt.frame {T : Tabs} {s t : State} (hp : SPre tsH tsG s)
    (h : TabsAt T.H T.dn T.f T.G T.g (stackArg s 16) (stackArg s 17) s) (hM : Frame (wrR s) s.mem t.mem)
    (hs : t.syms = s.syms) : TabsAt T.H T.dn T.f T.G T.g (stackArg s 16) (stackArg s 17) t :=
  ⟨by rw [tab_read hp hM (.inl rfl) (by decide), hs]; exact h.h0, by rw [tab_read hp hM (.inl rfl) (by decide), hs]; exact h.h3,
    by rw [tab_read hp hM (.inl rfl) (by decide), hs]; exact h.h4, by rw [tab_read hp hM (.inr rfl) (by decide), hs]; exact h.g0,
    by rw [tab_read hp hM (.inr rfl) (by decide), hs]; exact h.g1, by rw [tab_read hp hM (.inr rfl) (by decide), hs]; exact h.g2,
    by rw [tab_read hp hM (.inr rfl) (by decide)]; exact h.g4, by rw [hs]; exact h.hf, by rw [hs]; exact h.gf⟩

/-! ## The call -/

variable (T : Tabs) in
/-- What `encode` reads: the digest, the salt, the tables and its stack
arguments. -/
def eRd (s : State) : List Region :=
  [⟨stackArg s 10, T.H.D⟩, ⟨stackArg s 12, (stackArg s 13).toNat⟩, ⟨stackArg s 16, 56⟩, ⟨stackArg s 17, 56⟩,
    ⟨fb s, 32⟩]

/-- What it writes: the encoding's place, and its working space. -/
def eWr (s : State) (lo el : Nat) : List Region :=
  [⟨off (stackArg s 14) (oEm + lo), el⟩,
    ⟨off (stackArg s 14) oEnc, (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩]

/-- What the call of `encode` needs of the state before it. -/
structure EncAt (T : Tabs) (s t : State) (lo eb el : Nat) : Prop where
  sp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = frR s :: s.wr
  M : Frame (wrR s) s.mem t.mem
  sy : t.syms = s.syms
  w0 : word t.mem (fb s) (8 * 0) = off (stackArg s 14) oEnc
  w1 : word t.mem (fb s) (8 * 1) = stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)
  w2 : word t.mem (fb s) (8 * 2) = stackArg s 16
  w3 : word t.mem (fb s) (8 * 3) = stackArg s 17
  di : t.gpr .rdi = off (stackArg s 14) (oEm + lo)
  si : t.gpr .rsi = BitVec.ofNat 64 el
  dx : t.gpr .rdx = stackArg s 10
  cx : t.gpr .rcx = stackArg s 12
  r8 : t.gpr .r8 = stackArg s 13
  r9 : t.gpr .r9 = BitVec.ofNat 64 eb
  lo1 : lo ≤ 1
  eb1 : 1 ≤ eb
  eb2 : eb ≤ Proof.RsaPss.maxEmBits
  hel : el = Spec.RsaPss.emLength eb
  hD : T.H.D = (stackArg s 11).toNat
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 16) (stackArg s 17) s

theorem enc_pre {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} {s t : State} (hp : SPre tsH tsG s) {lo eb el : Nat}
    (E : EncAt T s t lo eb el) :
    (encK T Hs Gs).pre (t.callEntry.withRegions (eRd T s) (eWr s lo el)) := by
  have hsp := E.sp
  obtain hE0 := (stackArg_call hp hsp (eRd T s) (eWr s lo el) (i := 0) (by decide)).trans E.w0
  obtain hE1 := (stackArg_call hp hsp (eRd T s) (eWr s lo el) (i := 1) (by decide)).trans E.w1
  obtain hE2 := (stackArg_call hp hsp (eRd T s) (eWr s lo el) (i := 2) (by decide)).trans E.w2
  obtain hE3 := (stackArg_call hp hsp (eRd T s) (eWr s lo el) (i := 3) (by decide)).trans E.w3
  obtain hlo := E.lo1; have heb1 := E.eb1; have heb2 := E.eb2; have hel := E.hel
  obtain hel2 : el ≤ 1024 := by rw [hel]; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega_using [heb2]
  obtain fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  obtain fSE : Frame (wrR s) s.mem t.callEntry.mem := E.M.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
  obtain hTab : TabsAt T.H T.dn T.f T.G T.g (stackArg s 16) (stackArg s 17)
      (t.callEntry.withRegions (eRd T s) (eWr s lo el)) :=
    TabsAt.frame (t := t.callEntry.withRegions (eRd T s) (eWr s lo el)) hp E.tabs fSE (E.sy ▸ rfl)
  simp only [encK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    E.di, E.si, E.dx, E.cx, E.r8, E.r9, hsp, stackArgAddr_call hsp, hE0, hE1, hE2, hE3]
  obtain hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.k2
  obtain hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  obtain h8' := fb_sub8' hp
  obtain hsc : (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 15).toNat - 512 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 (oEnc / 8)).toNat = 512 from rfl]; omega_using [hsl]
  obtain toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]
  obtain hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega_using [hel2]
  obtain heb' : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega_using [heb2]
  rw [hel', heb', E.hD]
  -- What lies in what.
  obtain sI : Region.Sub ⟨off (stackArg s 14) (oEm + lo), el⟩ ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_using [hsl, c1, hlo, hel2])
  obtain sR : Region.Sub ⟨off (stackArg s 14) oEnc, (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c3])
  obtain sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := fun a h => frame_sub s a (Region.sub_prefix (by decide) a h)
  obtain sRet : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := ret8_sub s
  obtain sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 encStack, encStack⟩ (stkR s) := by
    simp only [stkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain sH : Region.Sub ⟨stackArg s 16, 56⟩ ⟨stackArg s 16, 88⟩ := Region.sub_prefix (by decide)
  obtain sG : Region.Sub ⟨stackArg s 17, 56⟩ ⟨stackArg s 17, 88⟩ := Region.sub_prefix (by decide)
  obtain dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega_using [])).symm
  obtain dKA : (⟨fb s - 8 - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 416) (k := 32) (by omega_using [])).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain dIR : (⟨off (stackArg s 14) (oEm + lo), el⟩ : Region).Disjoint
      ⟨off (stackArg s 14) oEnc, (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega_using [hlo, hel2, c1, c3])) (by omega_using [hsl, c1, hlo, hel2])
      (by rw [hsc]; omega_using [wS, c3, hsl])
  obtain hsA : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by unfold encStack; omega_arith, by omega_using [hF, h392, h8'], by rw [eRd, E.hD], rfl,
    (hp.ddgs.sub_right sI).symm, (hp.dsas.sub_right sI).symm, dIR, hsA.sub_left sI,
    hp.ddgs.sub_right sR, hp.dsas.sub_right sR, hsA.sub_left sR,
    (hp.dKs.sub_left sRet).sub_right sI, hp.dKdg.sub_left sRet, hp.dKsa.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    (hp.dKs.sub_left sStk).sub_right sI, hp.dKdg.sub_left sStk, hp.dKsa.sub_left sStk,
    (hp.dKs.sub_left sStk).sub_right sR, dKA,
    by rw [toNat_off (by omega_using [hsl, wS, c1, hlo, hel2])]; omega_using [hsl, wS, c1, hlo, hel2],
    hp.wDg, hp.wSa, by rw [toNat_off (by omega_using [hsl, wS, c3]), hsc]; omega_using [hsl, wS, c3],
    heb1, heb2, hel, by rw [hsc]; unfold Proof.RsaPss.encodingScratchWords; have := hp.k1; omega_using [hsl, this],
    ((hp.dstH.sub_left sI).sub_right sH), ((hp.dstG.sub_left sI).sub_right sG), ((hp.dstH.sub_left sR).sub_right sH),
    ((hp.dstG.sub_left sR).sub_right sG), (hp.dKtH.sub_left sRet).sub_right sH, (hp.dKtG.sub_left sRet).sub_right sG,
    (hp.dKtH.sub_left sStk).sub_right sH, (hp.dKtG.sub_left sStk).sub_right sG, by have := hp.wTH; omega_using [this],
    (by have := hp.wTG; omega_using [this]), hTab⟩

theorem enc_covers {T : Tabs} {s t : State} (hp : SPre tsH tsG s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    {lo el : Nat} (hlo : lo ≤ 1) (hel2 : el ≤ 1024) (hD : T.H.D = (stackArg s 11).toNat) :
    Covers (eRd T s ++ eWr s lo el) (t.rd ++ t.wr) ∧ Covers (eWr s lo el) t.wr := by
  have hsl := hp.hsl
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  obtain hsc : (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 15).toNat - 512 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 (oEnc / 8)).toNat = 512 from rfl]; omega_using [hsl]
  obtain hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  obtain hscr : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  obtain cw : Covers (eWr s lo el) t.wr := Covers.of_sub fun r hr => by
    simp only [eWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hscr, oEm + lo, rfl, by dsimp only; omega_using [hsl, c1, hlo, hel2]⟩
    · exact ⟨_, hscr, oEnc, rfl, by dsimp only; rw [hsc]; omega_using [hsl, c3]⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  obtain hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  simp only [eRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨stackArg s 10, (stackArg s 11).toNat⟩, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using [hD]⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨⟨stackArg s 16, 88⟩, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨⟨stackArg s 17, 88⟩, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
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
      rw [hF _ (fun p hp hc => hn ⟨p, hp, ?_⟩) (.inl (cS S (o := o) (n := 1) (by omega_using [ho]) |>.byte
        (by rw [BitVec.sub_self]; decide))), R.scr o ho]
      have := hrg p hp
      have := (Offset.lt_iff (off S o) S (d := p.1) (n := p.2) (by have := G'.Sw; unfold oRsa at *; omega_arith)).mp hc
      rwa [off, Mem.sub_ofNat_toNat S (by unfold oRsa at *; omega_using [ho])] at this
  fr k hk := by
    rw [← R.fr k hk]
    refine Mem.readW_congr fun i hi => hF _ (fun p hp hc => ?_) (.inr ?_)
    · have := hrg p hp
      exact G'.dFS _ ((cF F hk).byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]; omega_using [hi]))
        ((Offset.sub_base S (by omega_using [this]) : Region.Sub ⟨off S p.1, p.2⟩ ⟨S, oRsa⟩) _ hc)
    · exact (cF F hk).byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]; omega_using [hi])

theorem enc_call {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} {encN : String} {encC : Prog isa}
    (hv : ∀ s, (encK T Hs Gs).pre s → ∃ t s', Exec isa encC s t s' ∧ abiPreserved s s' ∧ (encK T Hs Gs).post s s')
    (hspC : SpSafe encC) (hd : encC.x86_64Depth ≤ encStack)
    {s t : State} (hp : SPre tsH tsG s) {lo eb el : Nat} (E : EncAt T s t lo eb el) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 14) V W) :
    WP isa (.call encN encC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (wrR s) s.mem t'.mem ∧ t'.syms = s.syms ∧
      Rep t'.mem (fb s) (stackArg s 14)
        (fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then t'.mem (off (stackArg s 14) o) else V o) W ∧
      match Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
          (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb with
      | some e => (t'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.bytesAt t'.mem (off (stackArg s 14) (oEm + lo)) el = e
      | none => (t'.gpr .rax).setWidth 32 = 0 := by
  obtain hst := E.sp; have hrd := E.rd; have hwr := E.wr; have hM := E.M
  obtain hlo := E.lo1; have hel := E.hel; have heb2 := E.eb2
  obtain hel2 : el ≤ 1024 := by rw [hel]; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega_using [heb2]
  obtain ⟨hc, hw⟩ := enc_covers (T := T) hp hrd hwr hlo hel2 E.hD
  refine X86_64.WP.of_syms (X86_64.WP.callF hv hspC (by unfold encStack at hd; omega_using [hd])
    (enc_pre (Hs := Hs) (Gs := Gs) hp E) hc hw ?_)
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx hsy
  obtain hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  obtain hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS; have hk1 := hp.k1
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  have c2 : oRsa = 8192 := rfl
  obtain hsc : (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 15).toNat - 512 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 (oEnc / 8)).toNat = 512 from rfl]; omega_using [hsl]
  rw [hst] at hf
  -- What the call writes, within what the function may write.
  obtain sI : Region.Sub ⟨off (stackArg s 14) (oEm + lo), el⟩ (scrR s) :=
    Offset.sub_base _ (by omega_using [hsl, c1, hlo, hel2])
  obtain sR : Region.Sub ⟨off (stackArg s 14) oEnc, (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ (scrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c3])
  obtain sBel : Region.Sub (below (fb s) (encC.x86_64Depth + 8)) (stkR s) := by
    simp only [below, fb, stkR, sub_sub']
    exact Offset.sub_below _ (by unfold encStack at hd; omega_using [hd, h392, hss])
      (by unfold encStack at hd; omega_using [hd, hss])
  obtain dFb : (frR s).Disjoint (below (fb s) (encC.x86_64Depth + 8)) :=
    Offset.base_disjoint_below (fb s) (by unfold encStack at hd; omega_using [hd, h392])
  obtain hS8 : Region.Sub ⟨stackArg s 14, oRsa⟩ (scrR s) := Region.sub_prefix (by omega_using [hsl, c2])
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), hsy.trans E.sy, ?_, ?_⟩
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
        obtain h1 := (Offset.lt_iff x (stackArg s 14) (d := oEnc) (n := (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8)
          (by rw [hsc]; omega_using [wS, c3, hsl])).mp (by simp only [Region.Contains, off] at hc; omega_using [hc])
        obtain h2 : (x - stackArg s 14).toNat < oRsa := by simp only [Region.Contains] at hin; omega_using [hin]
        show (x - (stackArg s 14 + BitVec.ofNat 64 oEnc)).toNat + 1 ≤ oRsa - oEnc
        have := (Offset.lt_iff x (stackArg s 14) (d := oEnc) (n := oRsa - oEnc) (by omega_using [c2, c3])).mpr
          ⟨h1.1, by omega_using [h2, c2, c3]⟩
        omega_using [this]
      · exact (hp.dKs.sub_left (frame_sub s)) x hin (sR x hc)
    · rcases hin with hin | hin
      · exact hp.dKs x (sBel x hc) (hS8 x hin)
      · exact dFb x hin hc
  · have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    obtain fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
    obtain b : ∀ {R : Region}, (stkR s).Disjoint R → (outR s).Disjoint R → R.Disjoint (scrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hO hS hl => bytesAt_frame fSE (in_apart hK hO hS) hl
    obtain hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega_using [hel2]
    obtain heb' : (BitVec.ofNat 64 eb).toNat = eb := by
      rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega_using [heb2]
    simp only [encK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      E.di, E.si, E.dx, E.cx, E.r8, E.r9, hm₂, hg₂ .rax (by decide), hel', heb'] at hpost
    rw [E.hD] at hpost ⊢
    rw [b (R := ⟨stackArg s 10, (stackArg s 11).toNat⟩) hp.dKdg hp.dOdg hp.ddgs (by have := hp.wDg; dsimp only; omega_using []),
      b (R := ⟨stackArg s 12, (stackArg s 13).toNat⟩) hp.dKsa hp.dOsa hp.dsas
        (by have := hp.wSa; dsimp only; omega_using [])] at hpost
    exact hpost

/-- The hash function of the table `hash`, at word 5 of the table. -/
theorem idx_read {s : State} (hp : SPre tsH tsG s) {m : Mem} (hM : Frame (wrR s) s.mem m) :
    m.readW (off (stackArg s 16) 40) 64 = s.mem.readW (off (stackArg s 16) 40) 64 := by
  have hw := hp.wTH
  refine hM.readW (r := ⟨stackArg s 16, 88⟩) (Offset.contains_base _ (by omega_using []) (by omega_using [])) (fun r hr => ?_) (by decide)
  simp only [wrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.dKtH.symm
  · exact hp.dOtH.symm
  · exact hp.dstH.symm

/-- What signing needs of the tables in the entry state `s`: the index `i`
of the hash function of `hash`, the functions `T` of both tables, the hash
functions `Hs` and `Gs` they name, and that `encode` for the index `i`
computes the encoding with them. -/
structure ESel (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) (s : State) (i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) : Prop where
  mem : i ∈ idxs
  idx : s.mem.readW (off (stackArg s 16) 40) 64 = BitVec.ofNat 64 i
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 16) (stackArg s 17) s
  hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some Hs
  hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some Gs
  hD : T.H.D = (stackArg s 11).toNat
  ok : ∀ s', (encK T Hs Gs).pre s' → ∃ t s'', Exec isa (encode f (ofIdx i) g) s' t s'' ∧ abiPreserved s' s'' ∧
    (encK T Hs Gs).post s' s''

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignCParams`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing and verification on x86-64, around the encoding: the
parameters

From the modulus' first byte `n₀ ≠ 0` in `rax` and its length `k`, `emBitsB`
stores `emBits = 8 (k - 1) + log₂ n₀`, `emLen = ⌈emBits / 8⌉` and
`lo = k - emLen` to their slots (`emBitsB_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

/-- The seven compares of `emBitsB`. -/
def sbbChain : List Instr := [.alu .cmp .rax (.imm 2), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 4), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 8), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 16), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 32), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 64), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 128), .alu .sbb .rdx (.imm 0)]

/-- What each compare of `sbbChain` subtracts: 1 if `x < c`. -/
abbrev cb (y : BitVec 64) (c : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.ofBool (decide (y.toNat < c.toNat)))

/-- The seven of them. -/
def cbSum (y : BitVec 64) : BitVec 64 :=
  cb y 2 + cb y 4 + cb y 8 + cb y 16 + cb y 32 + cb y 64 + cb y 128

theorem sub7 (d z a1 a2 a3 a4 a5 a6 a7 : BitVec 64) (hz : z = 0) :
    d - z - a1 - z - a2 - z - a3 - z - a4 - z - a5 - z - a6 - z - a7 =
      d - (a1 + a2 + a3 + a4 + a5 + a6 + a7) := by
  subst hz; simp [BitVec.sub_sub, BitVec.add_assoc]

theorem cbSum_table : ∀ x < 256, x ≠ 0 →
    ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ cbSum (BitVec.ofNat 64 x) = BitVec.ofNat 64 (7 - j) := by
  decide +kernel

theorem cbSum_eq {x : Nat} (hx : x < 256) (h0 : x ≠ 0) :
    cbSum (BitVec.ofNat 64 x) = BitVec.ofNat 64 (7 - Nat.log2 x) := by
  obtain ⟨j, _, hl, hu, he⟩ := cbSum_table x hx h0
  rw [he, RsaPss.log2_eq h0 hl hu]

/-- `rdx := 8 k - 1 - cbSum x`. -/
theorem sbbChain_ok (u : State) (x : BitVec 64) (d : BitVec 64) (hax : u.gpr .rax = x) (hdx : u.gpr .rdx = d) :
    WP isa (.block sbbChain) u fun u' => Keep [.rdx, .rax] u u' ∧ u'.mem = u.mem ∧ u'.gpr .rdx = d - cbSum x := by
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rdx = d - cbSum x) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [sbbChain, hax, hdx]
  rw [sub7 _ (BitVec.signExtend 64 0) _ _ _ _ _ _ _ (by decide)]
  simp only [cbSum, cb]
  rfl

/-- `emBits` from the modulus' length and first byte. -/
def ebV (k x : Nat) : Nat := 8 * (k - 1) + Nat.log2 x

theorem emBitsB_eq : emBitsB = ([.mov .rdx (.mem (sp sK)), .shift .shl .rdx 3, .alu .sub .rdx (.imm 1)] : List Instr) ++
    sbbChain ++ ([.store (sp sBits) .rdx, .mov .rax (.reg .rdx), .alu .add .rax (.imm 7), .shift .shr .rax 3,
      .store (sp sEml) .rax, .mov .r8 (.mem (sp sK)), .alu .sub .r8 (.reg .rax), .store (sp sLo) .r8] : List Instr) :=
  rfl

theorem emBitsB_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k x : Nat} (hk : W 17 = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hk2 : k ≤ 1024)
    (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block emBitsB) u fun u' => Lay u' F S ∧ Keep [.rdx, .rax, .r8] u u' ∧
      Rep u'.mem F S V (upd (upd (upd W 27 (BitVec.ofNat 64 (ebV k x))) 28
        (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)))) 26 (BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)))) := by
  have G := L.geo
  have hl8 : Nat.log2 x < 8 := (Nat.log2_lt h0).mpr (by omega_using [hx])
  have heb : ebV k x ≤ 8 * k - 1 := by unfold ebV; omega_using [hk1, hl8]
  have hel : Spec.RsaPss.emLength (ebV k x) ≤ k := by unfold Spec.RsaPss.emLength; omega_using [heb]
  rw [emBitsB_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun v => v.mem = u.mem ∧ v.gpr .rdx = BitVec.ofNat 64 (8 * k - 1)) ?_ rfl)
    fun v ⟨⟨hm, hd⟩, kv⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sK) (by decide), R.rd (d := sK) 17 rfl (by decide), hk]
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow]
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
    omega_using [hk1]
  refine WP.mono (sbbChain_ok v (BitVec.ofNat 64 x) _ (by rw [kv.gpr (by decide)]; exact hax) hd)
    fun w ⟨kw, hmw, hdw⟩ => ?_
  have hdw' : w.gpr .rdx = BitVec.ofNat 64 (ebV k x) := by
    rw [hdw, cbSum_eq hx h0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    unfold ebV; omega_using [hk1, hl8]
  have Lw : Lay w F S := L.congr ((kw.gpr (by decide)).trans (kv.gpr (by decide))) (kw.2.2.trans kv.2.2)
    (by rw [hmw, hm])
  have Rw : Rep w.mem F S V W := by rw [hmw, hm]; exact R
  have R1 := Rw.wf G (k := 27) (by decide) (BitVec.ofNat 64 (ebV k x))
  have R2 := R1.wf G (k := 28) (by decide) (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)))
  have R3 := R2.wf G (k := 26) (by decide) (BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)))
  rw [show off F (8 * 27) = off F sBits from rfl] at R1 R2 R3
  rw [show off F (8 * 28) = off F sEml from rfl] at R2 R3
  rw [show off F (8 * 26) = off F sLo from rfl] at R3
  have h17 : (((w.mem.writeW (off F sBits) (BitVec.ofNat 64 (ebV k x))).writeW (off F sEml)
      (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x))))).readW (off F sK) 64 = BitVec.ofNat 64 k := by
    have := R2.fr 17 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hk, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun y => y.mem = ((w.mem.writeW (off F sBits)
      (BitVec.ofNat 64 (ebV k x))).writeW (off F sEml) (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)))).writeW
      (off F sLo) (BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)))) ?_ rfl) fun y ⟨hmy, ky⟩ => ?_
  · have h7 : (BitVec.ofNat 64 (ebV k x) + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 =
        BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)) := by
      have hb : ebV k x < 8192 := by unfold ebV at *; omega_using [hk2, hl8]
      generalize ebV k x = e at hb ⊢
      rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 from rfl]
      unfold Spec.RsaPss.emLength
      bv_omega
    xrun [ea_sp, Lw.rsp, Lw.st (d := sBits) (by decide), Lw.st (d := sEml) (by decide), Lw.st (d := sLo) (by decide),
      Lw.ld (d := sK) (by decide), hdw', h7, h17, VG.Offset.ofNat_sub_ofNat hel]
  refine ⟨Lw.of_rep' Rw (hmy ▸ R3) (by simp [upd]) (ky.gpr (by decide)) ky.2.2,
    ((kv.trans kw).trans ky).mono (by decide), hmy ▸ R3⟩

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.ByIdx`, which this module and modules that import it used -/

section

/-!
# The choice of the code for the hash function of a table, on x86-64

`byIdx b is` runs `b i` for the index `i` in `r11`, by comparisons with each
of `is`: `byIdx_wp` from the state before the comparisons, `byIdx_ct` in two
runs whose `r11` is the same, each comparison keeping the state but its
flags.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The comparison of `r11` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))]

/-- What the comparisons with the indices `is` write and load: the flags. -/
def CmpOk (is : List Nat) : Prop :=
  ∀ j ∈ is, j < 2 ^ 31 ∧ VG.Proof.MlKem.X86_64.writesOnly [.r11] (cmpIdx j) = true ∧
    (cmpIdx j).allInstrs (fun i => !loadsMxcsr i) = true

theorem cmpOk_idxs : CmpOk idxs := by unfold CmpOk idxs; decide

/-- `WP.mono` that also keeps the symbols and MXCSR. -/
theorem WP.mono_mxs {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q R : State → Prop} (h : WP isa c s Q) (hq : ∀ s', Q s' → s'.syms = s.syms → s'.mxcsr = s.mxcsr → R s') :
    WP isa c s R :=
  WP.mono_mx hc (X86_64.WP.mono_syms h fun s' q sy => (⟨q, sy⟩ : Q s' ∧ s'.syms = s.syms))
    fun s' ⟨q, sy⟩ hx => hq s' q sy hx

/-- A comparison of `r11` with `j`: the state kept but for the flags. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 2 ^ 31) (hj : j < 2 ^ 31)
    (hw : VG.Proof.MlKem.X86_64.writesOnly [.r11] (cmpIdx j) = true) (h11 : t.gpr .r11 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))]) t fun t' => Keep [] t t' ∧ t'.mem = t.mem ∧
      t'.zf = some (decide (i = j)) ∧ t'.syms = t.syms := by
  refine WP.of_syms <| WP.mono (WP.keep [.r11] (Q := fun t' => t'.mem = t.mem ∧ t'.zf = some (decide (i = j)) ∧
    t'.gpr .r11 = t.gpr .r11) ?_ hw)
    fun t' ⟨⟨hm, hz, h11'⟩, k⟩ sy => ⟨⟨fun r _ => if e : r = .r11 then e ▸ h11' else k.gpr (by simpa using e), k.2.1,
      k.2.2⟩, hm, hz, sy⟩
  xrun [h11, VG.Proof.MlKem.X86_64.sx_ofNat hj,
    VG.Proof.Bignum.X86_64.ofNat_sub_beq (show i < 2 ^ 64 by omega_using [hi]) (show j < 2 ^ 64 by omega_using [hj])]

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → CmpOk is → t.gpr .r11 = BitVec.ofNat 64 i →
    (∀ t', Keep [] t t' → t'.mem = t.mem → t'.syms = t.syms → t'.mxcsr = t.mxcsr → WP isa (b i) t' Q) →
    WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi (List.not_mem_nil)
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t ⟨fun _ _ => rfl, rfl, rfl⟩ rfl rfl rfl
  | j :: k :: is, i, t, hi, hlt, h11, h => by
    have hil := (hlt i hi).1
    obtain ⟨hjl, hjw, hjm⟩ := hlt j (List.mem_cons_self ..)
    simp only [byIdx]
    refine WP.seq (WP.mono_mx hjm (cmpIdx_ok hil hjl hjw h11) fun t' ⟨k', hm, hz, sy⟩ hx => ?_)
    refine WP.ite (M := isa) _ (show isa.eval .e t' = _ from hz) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      subst hb
      exact h t' k' hm sy hx
    · rw [decide_eq_false_iff_not] at hb
      have hi' : i ∈ k :: is := (List.mem_cons.mp hi).resolve_left hb
      exact byIdx_wp hi' (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) ((k'.gpr (by simp)).trans h11)
        fun t'' k'' hm' sy' hx' => h t'' ⟨fun r hr => (k''.gpr hr).trans (k'.gpr hr), k''.2.1.trans k'.2.1,
          k''.2.2.trans k'.2.2⟩ (hm'.trans hm) (sy'.trans sy) (hx'.trans hx)

/-- `byIdx b is` in two runs whose `r11` is the index `idx a` of the
anchor: the comparisons from the same public `r11`, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → Keep [] t t' → t'.mem = t.mem → t'.syms = t.syms → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .r11 = BitVec.ofNat 64 (idx a)) →
    CmpOk is →
    (∀ j ∈ is, RelCT isa (Two Φ) (cmpIdx j) fun _ _ => True) →
    (∀ j ∈ is, RelCT isa (Two fun a t => Φ a t ∧ idx a = j) (b j) Q) →
    RelCT isa (Two Φ) (byIdx b is) Q
  | [], _, _, hΦ, _, _, _ => RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by simpa using (hΦ a _ h₁).1
  | [j], _, _, hΦ, _, _, hb => (hb j (List.mem_singleton_self _)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁, List.mem_singleton.mp (hΦ a _ h₁).1⟩, ⟨h₂, List.mem_singleton.mp (hΦ a _ h₁).1⟩⟩)
    fun _ _ h => h
  | j :: k :: is, Φ, hkeep, hΦ, hlt, hc, hb => by
    simp only [byIdx]
    have ih := byIdx_ct idx (is := k :: is) (Φ := fun a t => Φ a t ∧ idx a ≠ j)
      (fun a t t' ⟨h, hn⟩ k' hm sy => ⟨hkeep a t t' h k' hm sy, hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h)
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩)
        fun _ _ h => h)
    refine RelCT.seq (two_post (Ψ := fun a t => Φ a t ∧ t.zf = some (decide (idx a = j)))
      (hc j (List.mem_cons_self ..)) fun a t h => ?_) (two_ite (fun a t₁ t₂ h₁ h₂ => ?_)
        ((hb j (List.mem_cons_self ..)).mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h)
        (ih.mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h))
    · obtain ⟨hm, h11⟩ := hΦ a t h
      exact WP.mono (cmpIdx_ok (hlt _ hm).1 (hlt j (List.mem_cons_self ..)).1
        (hlt j (List.mem_cons_self ..)).2.1 h11)
        fun t' ⟨k', hm', hz, sy⟩ => ⟨hkeep a t t' h k' hm' sy, hz⟩
    · show t₁.zf = t₂.zf; rw [h₁.2, h₂.2]
    · rw [show isa.eval .e t = t.zf from rfl, hz] at he
      simpa using he
    · rw [show isa.eval .e t = t.zf from rfl, hz] at he
      simpa using he

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS signing on x86-64, around the encoding: correctness

`signC_ok`: from the entry state, `signC` refuses a modulus whose first
byte is zero, computes `emBits`, calls `encode` for the hash function of
the table `hash` (by its index, `byIdx`) for the encoding at
`scratch + oEm + lo` after a zero byte, and, if it fits, the private-key
operation on those `k` bytes, which leaves `out` and `rax` as
`RsaPss.sign` says (`sign_encode₂`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {tsH tsG : List FnTable}

/-- `encode`'s return value, tested. -/
theorem test32_ok (u : State) :
    WP isa (.block [.alu32 .test .rax (.reg .rax)]) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.zf = some (decide ((u.gpr .rax).setWidth 32 = 0)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧
      u'.zf = some (decide ((u.gpr .rax).setWidth 32 = 0))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun []
  rw [BitVec.and_self, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

/-- `lo = k - emLen` is 0 or 1. -/
theorem lo_le {k x : Nat} (hx : Nat.log2 x < 8) (hk : 1 ≤ k) : k - Spec.RsaPss.emLength (ebV k x) ≤ 1 := by
  unfold Spec.RsaPss.emLength ebV; omega

/-- The bytes the private-key operation reads: a zero byte (if `lo = 1`),
then the encoding. -/
theorem em_input {m : Mem} {S : Addr} {V : Nat → Byte} {lo el k : Nat} {e : List Byte} (hk : lo + el = k)
    (hlo : lo ≤ 1) (he : Spec.Rsa.bytesAt m (off S (oEm + lo)) el = e) :
    (List.range k).map (fun i => (fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then m (off S o)
      else upd V oEm 0 o) (oEm + i)) = Spec.RsaPss.zeros lo ++ e := by
  subst he
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  apply List.ext_getElem
  · simp [Spec.RsaPss.zeros, Spec.Rsa.bytesAt]; omega_using [hk]
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < lo
  · rw [ifn (fun ⟨p, hp, a, b⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only at a b <;> omega_arith)]
    rw [List.getElem_append_left (by simp [Spec.RsaPss.zeros]; omega_using [hi])]
    simp only [upd, Spec.RsaPss.zeros, List.getElem_replicate]
    rw [ifp (by omega_using [hlo, hi])]
  · rw [ifp ⟨_, List.mem_cons_self .., by dsimp only; omega_using [hi], by dsimp only; omega_using [hk, h1]⟩]
    rw [List.getElem_append_right (by simp [Spec.RsaPss.zeros]; omega_using [hi])]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Spec.RsaPss.zeros, List.length_replicate,
      off_plus]
    congr 2; omega_using [hi]

/-- The slots after `idxSlot`. -/
def proW1 (s : State) : Nat → BitVec 64 := upd (proW s) 47 (s.mem.readW (off (stackArg s 16) 40) 64)

/-- The table `hash` to `r11`, the flags kept. -/
theorem r11Arg_ok {s u : State} (hp : SPre tsH tsG s) (hsp : u.gpr .rsp = fb s) (hrd : u.rd = s.rd)
    (hA : ArgsKept s u.mem) :
    WP isa (.block [.mov .r11 (.mem (arg 16))]) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r11 = stackArg s 16 ∧ u'.zf = u.zf := by
  obtain hF := fb_toNat hp
  have := hp.sp2
  obtain hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * 16)) 8 := by
    rw [argAddr]; exact hp.argIn hrd (by decide)
  obtain hv : u.mem.readW (off (fb s) (frameBytes + 8 + 8 * 16)) 64 = stackArg s 16 := by
    rw [argAddr]; exact hA 16 (by decide)
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = stackArg s 16 ∧ u'.zf = u.zf) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [arg, ea_sp, hsp, hin, hv]

/-- The index of the table `hash`'s hash function to its slot, the flags
kept. -/
theorem idxSlot_ok {s u : State} (hp : SPre tsH tsG s) (L : Lay u (fb s) (stackArg s 14)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 14) V W) (hrd : u.rd = s.rd)
    (hM : Frame (wrR s) s.mem u.mem) (h11 : u.gpr .r11 = stackArg s 16) :
    WP isa (.block idxSlot) u fun u' => Lay u' (fb s) (stackArg s 14) ∧ Keep [.r11] u u' ∧
      Rep u'.mem (fb s) (stackArg s 14) V (upd W 47 (s.mem.readW (off (stackArg s 16) 40) 64)) ∧ u'.zf = u.zf ∧
      Frame (wrR s) s.mem u'.mem := by
  have hw := hp.wTH
  have G' := L.geo
  obtain hin : InRegions (u.rd ++ u.wr) (off (stackArg s 16) 40) 8 :=
    ⟨⟨stackArg s 16, 88⟩, hp.rdIn hrd (by simp),
      Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  obtain R1 := R.wf G' (k := 47) (by decide) (s.mem.readW (off (stackArg s 16) 40) 64)
  rw [show off (fb s) (8 * 47) = off (fb s) sIdx from rfl] at R1
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) sIdx)
      (s.mem.readW (off (stackArg s 16) 40) 64) ∧ u'.zf = u.zf) ?_ rfl) fun u' ⟨⟨hm, hz⟩, k⟩ => ?_
  · xrun [idxSlot, ea_at, ea_sp, L.rsp, h11, hin, idx_read hp hM, L.st (d := sIdx) (by decide)]
  obtain R' := hm ▸ R1
  refine ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, R', hz, ?_⟩
  rw [hm]
  exact hM.trans ((frame_w hp (Frame.refl _ _) (d := sIdx) (by decide) _).sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩)

/-- The index to `r11`. -/
theorem idxLoad_ok {s u : State} (L : Lay u (fb s) (stackArg s 14)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) (stackArg s 14) V W) :
    WP isa (.block idxLoad) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r11 = W 47 := by
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = W 47) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [idxLoad, ea_sp, L.rsp, L.ld (d := sIdx) (by decide), R.rd (d := sIdx) 47 rfl (by decide)]

/-- `emBits`, then `encode`'s arguments but the tables. -/
theorem encPrep_ok {s u : State} (L : Lay u (fb s) (stackArg s 14)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) (stackArg s 14) V W) (h17 : W 17 = s.gpr .rcx) (h22 : W 22 = stackArg s 15)
    (h37 : W 37 = stackArg s 10) (h39 : W 39 = stackArg s 12) (h40 : W 40 = stackArg s 13)
    (hk1 : 1 ≤ (s.gpr .rcx).toNat)
    (hk2 : (s.gpr .rcx).toNat ≤ 1024) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block (emBitsB ++ (encA1 ++ encA2 ++ encA3))) u fun u' => Lay u' (fb s) (stackArg s 14) ∧
      Keep [.rdx, .rax, .r8, .rdi, .rax, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Rep u'.mem (fb s) (stackArg s 14) (upd V oEm 0)
        (upd (upd (upd (upd (upd W 27 (BitVec.ofNat 64 (ebV (s.gpr .rcx).toNat x))) 28
          (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)))) 26
          (BitVec.ofNat 64 ((s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)))) 0
          (off (stackArg s 14) oEnc)) 1 (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8))) ∧
      u'.gpr .rdi = off (stackArg s 14) (oEm + ((s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))) ∧
      u'.gpr .rsi = BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)) ∧
      u'.gpr .rdx = stackArg s 10 ∧ u'.gpr .rcx = stackArg s 12 ∧ u'.gpr .r8 = stackArg s 13 ∧
      u'.gpr .r9 = BitVec.ofNat 64 (ebV (s.gpr .rcx).toNat x) := by
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok L R (k := (s.gpr .rcx).toNat) (x := x)
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk1 hk2 hx h0 hax) fun t ⟨L3, k3, R3⟩ => ?_
  exact WP.mono (encArgs3_ok L3 R3 (lo := (s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))
    (eb := ebV (s.gpr .rcx).toNat x) (el := Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))
    (dig := stackArg s 10) (q := stackArg s 12) (sl := stackArg s 13) (sw := stackArg s 15)
    (by simp [upd, h22]) (by simp [upd]) (by simp [upd]) (by simp [upd]) (by simp [upd, h37])
    (by simp [upd, h39]) (by simp [upd, h40]))
    fun t' ⟨L4, k4, R4, a, b, c, d, e, f⟩ => ⟨L4, k3.trans k4, R4, a, b, c, d, e, f⟩

/-- Bytes of the working space, as two memories with the same bytes there
give them. -/
theorem Rep.bytes_eq {m₁ m₂ : Mem} {F S : Addr} {V : Nat → Byte} {W₁ W₂ : Nat → BitVec 64}
    (R₁ : Rep m₁ F S V W₁) (R₂ : Rep m₂ F S V W₂) {o n : Nat} (h : o + n ≤ oRsa) :
    Spec.Rsa.bytesAt m₁ (off S o) n = Spec.Rsa.bytesAt m₂ (off S o) n := by
  rw [bytesAt_off, bytesAt_off]
  exact List.map_congr_left fun i hi => by
    have := List.mem_range.mp hi
    rw [R₁.scr _ (by omega_using [h, this]), R₂.scr _ (by omega_using [h, this])]

/-- The private-key operation's arguments `args` and its call, as `signC`
needs them: from the frame after the test of `encode`'s result, they leave
the frame's last words (the saved registers), the callee-saved registers,
MXCSR's control bits and the working space, and `out` as
`Rsa.privateChecked` says on the `k` bytes at `scratch + oEm`. -/
def PStep (args : List Instr) (privN : String) (privC : Prog isa) (s : State) : Prop :=
  ∀ (u : State) (V : Nat → Byte) (W : Nat → BitVec 64), Lay u (fb s) (stackArg s 14) → u.rd = s.rd →
    u.wr = frR s :: s.wr → Frame (wrR s) s.mem u.mem → Rep u.mem (fb s) (stackArg s 14) V W →
    W 16 = s.gpr .rdi → W 17 = s.gpr .rcx → W 18 = s.gpr .rdx → W 19 = s.gpr .r8 → W 20 = s.gpr .r9 →
    W 22 = stackArg s 15 →
    WP isa (.seq (.block args) (.call privN privC)) u fun u' => ∃ W', Lay u' (fb s) (stackArg s 14) ∧
      u'.wr = u.wr ∧ (∀ r ∈ [Reg.r13, .r14, .r15], u'.gpr r = u.gpr r) ∧
      u'.mxcsr.extractLsb' 6 10 = u.mxcsr.extractLsb' 6 10 ∧ Rep u'.mem (fb s) (stackArg s 14) V W' ∧
      (∀ j, 40 < j → j < nW → W' j = W j) ∧
      Spec.Rsa.writtenOutcome u'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt u.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- `signC`'s frame, with the arguments `args` of the private-key operation,
which `PStep` describes. -/
theorem signCWith_ok {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {privN : String} {privC : Prog isa}
    {args : List Instr}
    (hspE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g)) (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    {s : State} (hp : SPre tsH tsG s) (hstep : PStep args privN privC s)
    {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} (E : ESel f g s i T Hs Gs) :
    WP isa (.frame (.alloc frameBytes) (signCBodyWith f g privN privC args) (.free frameBytes)) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (signK tsH tsG).post s s' ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  obtain hF := fb_toNat hp
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hHl : Hs.len = T.H.D := ((hp.hdl Hs E.hH).symm.trans E.hD.symm)
  refine wp_frame (by have := hp.sp1; unfold signStack Rsa.X86_64.stackBytes frameBytes at *; omega_arith) ?_
  rw [signCBodyWith]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_mxs (by decide) (signPro_ok hp)
    fun t1 ⟨k1, L1, R1, f1⟩ sy1 hx1 => ?_
  refine WP.mono_mxs (by decide) (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1))
    fun t2 ⟨k2, hm2, hax2, hz2⟩ sy2 hx2 => ?_
  obtain L2 : Lay t2 (fb s) (stackArg s 14) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  obtain hM2 : Frame (wrR s) s.mem t2.mem := hm2 ▸ frame_wrR f1
  refine WP.mono_mxs (by decide) (r11Arg_ok hp L2.rsp (k2.2.1.trans k1.2.1) (argsKept_of hp hM2))
    fun t2' ⟨k2', hm2', h11, hz2'⟩ sy2' hx2' => ?_
  obtain L2' : Lay t2' (fb s) (stackArg s 14) := L2.congr (k2'.gpr (by decide)) k2'.2.2 (by rw [hm2'])
  refine WP.seq (WP.mono_mxs (by decide) (idxSlot_ok hp L2' (hm2' ▸ hm2 ▸ R1)
      (k2'.2.1.trans (k2.2.1.trans k1.2.1)) (hm2' ▸ hM2) h11)
    fun t3 ⟨L3, k3, R3, hz3, hM3⟩ sy3 hx3 => ?_)
  obtain hw3 : t3.wr = frR s :: s.wr := k3.2.2.trans (k2'.2.2.trans (k2.2.2.trans k1.2.2))
  obtain hrd3 : t3.rd = s.rd := k3.2.1.trans (k2'.2.1.trans (k2.2.1.trans k1.2.1))
  obtain hsy3 : t3.syms = s.syms := sy3.trans (sy2'.trans (sy2.trans sy1))
  obtain hcs3 : ∀ r ∈ [Reg.r13, .r14, .r15], t3.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.r11] ∧ r ∉ [Reg.rsi, .rax] ∧ r ∉ [Reg.rax] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k3.gpr this.1, k2'.gpr this.1, k2.gpr this.2.1, k1.gpr this.2.2]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  obtain hax3 : t3.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), hax2]
  refine WP.seq (WP.mono (Q := SDone s) ?_ fun t D => restore_ok hp D)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdx) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdx + 1) ((s.gpr .rcx).toNat - 1) with hrest
  obtain hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega_arith)
  obtain hrl : rest.length = (s.gpr .rcx).toNat - 1 := by simp [hrest, Spec.Rsa.bytesAt]
  obtain hHs : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some G → H = Hs ∧ G = Gs := fun H G a b =>
    ⟨Option.some.inj (a.symm.trans E.hH), Option.some.inj (b.symm.trans E.hG)⟩
  obtain hx3' : t3.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx3, hx2', hx2, hx1]; rfl
  refine WP.ite (M := isa) _ (show isa.eval .e t3 = _ by rw [show isa.eval .e t3 = t3.zf from rfl, hz3, hz2', hz2])
    (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    obtain h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine fail_done hp L3 R3 hw3 hcs3 (by simp [proW, upd]) (by simp [proW, upd]) (by simp [proW, upd])
      (by simp [proW, upd]) (by simp [proW, upd]) (fun H G _ _ => ?_) hx3'
    rw [signOut, hnB, h0]; exact RsaPss.sign_zero₂ ..
  rw [decide_eq_false_iff_not] at hb
  obtain h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  obtain hl8 := RsaPss.log2_lt8 n₀
  set k := (s.gpr .rcx).toNat with hk
  set eb := ebV k n₀.toNat with heb_def
  set el := Spec.RsaPss.emLength eb with hel_def
  set lo := k - el with hlo_def
  obtain hlo : lo ≤ 1 := lo_le hl8 (by omega_arith)
  obtain heb : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) k)) - 1 = eb := by
    rw [hnB, RsaPss.emBits_eq rest h0, hrl]; rfl
  obtain heb1 : 1 ≤ eb := by rw [heb_def]; unfold ebV; omega_arith
  obtain heb2 : eb ≤ Proof.RsaPss.maxEmBits := by
    rw [heb_def]; unfold ebV Proof.RsaPss.maxEmBits; omega_arith
  obtain hlok : lo + el = k := by
    rw [hlo_def, hel_def, heb_def]; unfold Spec.RsaPss.emLength ebV; omega_arith
  -- `emBits`, `encode`'s arguments, and the index.
  obtain eA : emBitsB ++ encArgs ++ idxLoad = emBitsB ++ (encA1 ++ encA2 ++ encA3) ++ (encA4 ++ idxLoad) := by
    simp only [encArgs_eq, List.append_assoc]
  refine WP.seq ?_
  rw [eA, WP.block_append_iff]
  refine WP.mono_mxs (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encPrep_ok L3 R3 (by simp [proW, upd]) (by simp [proW, upd]) (by simp [proW, upd])
      (by simp [proW, upd]) (by simp [proW, upd]) (by omega_arith) hk2 n₀.isLt hb hax3))
    fun t4 ⟨⟨L4, k4, R4, h4di, h4si, h4dx, h4cx, h48, h49⟩, f4⟩ sy4 hx4 => ?_
  obtain hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans hw3
  obtain hrd4 : t4.rd = s.rd := k4.2.1.trans hrd3
  obtain hM4 : Frame (wrR s) s.mem t4.mem := frame_keep hp hw3 L3.rsp hM3 f4
  rw [WP.block_append_iff]
  refine WP.mono_mxs (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encA4_ok hp L4 R4 hrd4 (argsKept_of hp hM4)))
    fun t5 ⟨⟨L5, k5, R5⟩, f5⟩ sy5 hx5 => ?_
  obtain hM5 : Frame (wrR s) s.mem t5.mem := frame_keep hp hw4 L4.rsp hM4 f5
  refine WP.mono_mxs (by decide) (idxLoad_ok L5 R5)
    fun t6 ⟨k6, hm6, h116⟩ sy6 hx6 => ?_
  set W6 := upd (upd (upd (upd (upd (upd (upd (proW1 s) 27 (BitVec.ofNat 64 eb)) 28 (BitVec.ofNat 64 el)) 26
    (BitVec.ofNat 64 lo)) 0 (off (stackArg s 14) oEnc)) 1 (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8))) 2
    (stackArg s 16)) 3 (stackArg s 17) with hW6
  obtain R6 : Rep t6.mem (fb s) (stackArg s 14) (upd (fun o => s.mem (off (stackArg s 14) o)) oEm 0) W6 := hm6 ▸ R5
  obtain L6 : Lay t6 (fb s) (stackArg s 14) := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  obtain hi11 : t6.gpr .r11 = BitVec.ofNat 64 i := by
    rw [h116, ← E.idx]; simp [upd]
  obtain hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (k5.2.2.trans hw4)
  obtain hrd6 : t6.rd = s.rd := k6.2.1.trans (k5.2.1.trans hrd4)
  obtain hM6 : Frame (wrR s) s.mem t6.mem := hm6 ▸ hM5
  obtain hsy6 : t6.syms = s.syms := sy6.trans (sy5.trans (sy4.trans hsy3))
  obtain g46 : ∀ r, r ∉ [Reg.rax, .r11] → t6.gpr r = t4.gpr r := fun r hr => by
    rw [k6.gpr (fun h => hr (by simp at h ⊢; exact .inr h)), k5.gpr (fun h => hr (by simp at h ⊢; exact .inl h))]
  obtain hx6' : t6.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx6, hx5, hx4]; exact hx3'
  -- The index chooses `encode`.
  refine WP.seq (byIdx_wp (i := i) E.mem cmpOk_idxs hi11 fun t7 k7 hm7 sy7 hx7 => ?_)
  obtain R7 : Rep t7.mem (fb s) (stackArg s 14) (upd (fun o => s.mem (off (stackArg s 14) o)) oEm 0) W6 := hm7 ▸ R6
  obtain g7 : ∀ r, t7.gpr r = t6.gpr r := fun r => k7.gpr (List.not_mem_nil)
  obtain EA : EncAt T s t7 lo eb el :=
    { sp := (g7 _).trans L6.rsp, rd := k7.2.1.trans hrd6, wr := k7.2.2.trans hw6, M := hm7 ▸ hM6,
      sy := sy7.trans hsy6, w0 := (R7.fr 0 (by decide)).trans (by simp [hW6, upd]),
      w1 := (R7.fr 1 (by decide)).trans (by simp [hW6, upd]), w2 := (R7.fr 2 (by decide)).trans (by simp [hW6, upd]),
      w3 := (R7.fr 3 (by decide)).trans (by simp [hW6, upd]),
      di := (g7 _).trans ((g46 _ (by decide)).trans h4di), si := (g7 _).trans ((g46 _ (by decide)).trans h4si),
      dx := (g7 _).trans ((g46 _ (by decide)).trans h4dx), cx := (g7 _).trans ((g46 _ (by decide)).trans h4cx),
      r8 := (g7 _).trans ((g46 _ (by decide)).trans h48), r9 := (g7 _).trans ((g46 _ (by decide)).trans h49),
      lo1 := hlo, eb1 := heb1, eb2 := heb2, hel := rfl, hD := E.hD, tabs := E.tabs }
  refine WP.mono (enc_call (Hs := Hs) (Gs := Gs) E.ok (hspE i E.mem) (hdE i E.mem) hp EA R7)
    fun t8 ⟨rd8, wr8, cs8, mx8, hM8, sy8, R8, hE⟩ => ?_
  set V8 := fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then t8.mem (off (stackArg s 14) o)
    else upd (fun o => s.mem (off (stackArg s 14) o)) oEm 0 o with hV8
  obtain L8 : Lay t8 (fb s) (stackArg s 14) := (L6.congr ((g7 _)) (k7.2.2) (by rw [hm7])).of_rep' R7 R8 rfl
    (cs8 .rsp (by decide)) wr8
  -- Its result, tested.
  refine WP.seq (WP.mono_mx (by decide) (test32_ok t8) fun t9 ⟨k9, hm9, hz9⟩ hx9 => ?_)
  obtain L9 : Lay t9 (fb s) (stackArg s 14) := L8.congr (k9.gpr (by decide)) k9.2.2 (by rw [hm9])
  obtain R9 : Rep t9.mem (fb s) (stackArg s 14) V8 W6 := by rw [hm9]; exact R8
  obtain hM9 : Frame (wrR s) s.mem t9.mem := by rw [hm9]; exact hM8
  obtain hw9 : t9.wr = frR s :: s.wr := k9.2.2.trans (wr8.trans (k7.2.2.trans hw6))
  obtain hrd9 : t9.rd = s.rd := k9.2.1.trans (rd8.trans (k7.2.1.trans hrd6))
  obtain hcs9 : ∀ r ∈ [Reg.r13, .r14, .r15], t9.gpr r = s.gpr r := fun r hr => by
    obtain h1 : r ∈ calleeSaved := by simp at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [k9.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs8 r h1, g7,
      g46 r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k4.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs3 r hr]
  obtain hmx9 : t9.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx9, mx8, hx7]; exact hx6'
  refine WP.ite (M := isa) _ (show isa.eval .e t9 = _ from hz9) (fun hb9 => ?_) (fun hb9 => ?_)
  · -- No encoding: refused.
    rw [decide_eq_true_eq] at hb9
    refine fail_done hp L9 R9 hw9 hcs9 (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (fun H G a b => ?_) hmx9
    obtain ⟨rfl, rfl⟩ := hHs H G a b
    rw [signOut, RsaPss.sign_encode₂ H G heb, hHl]
    cases he : Spec.RsaPss.encode H G (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb with
    | none => rfl
    | some e =>
      rw [he] at hE
      obtain ⟨h1, -⟩ := hE
      exact absurd (hb9.symm.trans h1) (by decide)
  rw [decide_eq_false_iff_not] at hb9
  obtain ⟨e, he, hbytes⟩ : ∃ e, Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb = some e ∧
      Spec.Rsa.bytesAt t8.mem (off (stackArg s 14) (oEm + lo)) el = e := by
    cases he : Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb with
    | none => rw [he] at hE; exact absurd hE hb9
    | some e => rw [he] at hE; exact ⟨e, rfl, hE.2⟩
  -- The private-key operation's arguments and call.
  refine WP.mono (hstep t9 _ W6 L9 hrd9 hw9 hM9 R9 (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (by simp [hW6, proW1, proW, upd]))
    fun u3 ⟨W2, L3', wr3, cs3, mx3, R3', w, hout3⟩ => ?_
  refine ⟨L3', wr3.trans hw9, fun r hr => (cs3 r hr).trans (hcs9 r hr), ?_, ?_, ?_, fun H G a b => ?_,
    by rw [mx3]; exact hmx9⟩
  · rw [R3'.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide)]; simp [hW6, proW1, proW, upd]
  · rw [R3'.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide)]; simp [hW6, proW1, proW, upd]
  · rw [R3'.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide)]; simp [hW6, proW1, proW, upd]
  · obtain ⟨rfl, rfl⟩ := hHs H G a b
    obtain hem : Spec.Rsa.bytesAt t9.mem (off (stackArg s 14) oEm) k = Spec.RsaPss.zeros lo ++ e := by
      rw [bytesAt_off, List.map_congr_left fun i hi => R9.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega_arith)]
      exact em_input hlok hlo hbytes
    rw [hem] at hout3
    rw [signOut, RsaPss.sign_encode₂ H G heb, hHl, he, bytesAt_length]
    exact hout3

end VG.Proof.RsaPss.X86_64
