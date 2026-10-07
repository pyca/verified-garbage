import VerifiedGarbage.Impl.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12

/-!
# ML-KEM on x86-64: `vg_mlkem_decode12_avx2`

The eight values of a group of 12 bytes are the candidates of
`vg_mlkem_sample_ntt4_avx2` (`S4.cand_dword`; for the last group, loaded 4
bytes early, `cand_dword'`), each reduced by `cadd32 (x - q)` (`red_val`);
the loop stores eight coefficients at a time (`D12Y.Inv`).
-/

namespace VG.Proof.MlKem.X86_64.D12Y

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open S4 (shuf0 shuf1 shV maskV qV4 candN cb candV cand_dword LUpd wp_vbin wp_vvar wp_vbcast128 wp_vst256
  GUpd wp_addi' itT itF ext_app2 toNat_dword_ofBytes toNat_and_fff dword_qV4 candN_lt)

/-! ## The masks of the last group -/

def shuf0' : BitVec 128 := 0x80800908808008078080060580800504#128
def shuf1' : BitVec 128 := 0x80800f0e80800e0d80800c0b80800b0a#128

theorem pshufb_shuf0' (a : BitVec 128) : XBinOp.eval .pshufb a shuf0' =
    ofBytes fun i => if i % 4 < 2 then byte a (4 + cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_shuf1' (a : BitVec 128) : XBinOp.eval .pshufb a shuf1' =
    ofBytes fun i => if i % 4 < 2 then byte a (10 + cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- The `vpshufb` mask of lane `l` for the last group. -/
abbrev shuf' (l : Nat) : BitVec 128 := if l = 0 then shuf0' else shuf1'

/-- The values in lane `l` of `ymm0`, from `a`, the 16 bytes in both, for the last group. -/
abbrev candV' (a : BitVec 128) (l : Nat) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb a (shuf' l)) shV) maskV

theorem cand_dword' (a : BitVec 128) {l j : Nat} (hl : l < 2) (hj : j < 4) :
    dword (candV' a l) j = BitVec.ofNat 32 (candN (fun i => (byte a (4 + i)).toNat) (4 * l + j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_pand, (show ∀ i < 4, dword maskV i = 0xfff#32 by decide) j hj, toNat_and_fff]
  have hb : ∀ i, (byte a i).toNat < 256 := fun i => (byte a i).isLt
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [shuf', VVarOp.eval, pshufb_shuf0', pshufb_shuf1', dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, ↓reduceIte, show (dword shV 0).toNat = 0 from rfl, show (dword shV 1).toNat = 4 from rfl,
    show (dword shV 2).toNat = 0 from rfl, show (dword shV 3).toNat = 4 from rfl, Nat.reduceLT,
    BitVec.toNat_ushiftRight,
    toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
    candN, cb, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceEqDiff, Nat.add_zero] <;>
  omega

/-! ## The constants -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movImm {d : Reg} {v : BitVec 64} (k : ∀ s', GUpd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.movImm64 d v :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', GUpd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_vpbcastd' {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun _ => let v := dword (s.xmm a) 0; ofDwords v v v v) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastd .l256 d a) :: is)) s Q := S4.wp_vpbcastd k

theorem wp_vsh {op : XShiftOp} {d a : XReg} {n : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => op.eval (s.lane a l) n) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vshift op .l256 d a n) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.eval (s.lane a 0) n) (op.eval (s.lane a 1) n)) rfl (k _ (by
    have h := LUpd.setV256 s d (op.eval (s.lane a 0) n) (op.eval (s.lane a 1) n)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_subi' {d : Reg} {v : BitVec 32}
    (k : ∀ s', GUpd s s' d (s.gpr d - v.signExtend 64) → s'.zf = some (s.gpr d - v.signExtend 64 == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.withFlags _ _ _ _ _ _ _) rfl)

theorem wp_vzu (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vop .vzeroupper :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl)

theorem wp_vmovq {d : XReg} {g : Reg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then (0 : BitVec 64) ++ s.gpr g else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vmovq d g) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV128 s d _ 0))

theorem wp_vbin128 {op : VBinOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then op.sse.eval (s.lane a 0) (s.lane b 0) else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l128 d a b) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV128 s d _ (op.sse.eval (s.lane a 1) (s.lane b 1))))

theorem wp_vinsert1 {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.lane a 0 else s.lane b 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vinserti128 d a b 1) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV256 s d _ _))

theorem wp_vpbcastq {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun _ => qword (s.xmm a) 0 ++ qword (s.xmm a) 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastq .l256 d a) :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (qword (s.xmm a) 0 ++ qword (s.xmm a) 0)
    (qword (s.xmm a) 0 ++ qword (s.xmm a) 0)) rfl (k _ ?_)
  have h := LUpd.setV256 s d (qword (s.xmm a) 0 ++ qword (s.xmm a) 0) (qword (s.xmm a) 0 ++ qword (s.xmm a) 0)
  exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr⟩

end

theorem qword_zero_app (x : BitVec 64) : qword ((0 : BitVec 64) ++ x) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

/-- `yconst4 r q₀ q₁ q₂ q₃`: the lanes of `ymm r` are `q₁ ++ q₀` and `q₃ ++ q₂`. -/
theorem yconst4_ok {r : XReg} (hr0 : r ≠ .xmm0) (hr1 : r ≠ .xmm1) (q₀ q₁ q₂ q₃ : BitVec 64) {is : List Instr}
    {s : State} {Q : State → Prop}
    (k : ∀ s', s'.lane r 0 = (q₁ ++ q₀ : BitVec 128) → s'.lane r 1 = (q₃ ++ q₂ : BitVec 128) →
      (∀ x, x ≠ r → x ≠ .xmm0 → x ≠ .xmm1 → ∀ l < 2, s'.lane x l = s.lane x l) →
      (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (yconst4 r q₀ q₁ q₂ q₃ ++ is)) s Q := by
  simp only [yconst4, List.cons_append, List.nil_append]
  refine wp_movImm fun s1 u1 => wp_vmovq fun s2 u2 => wp_movImm fun s3 u3 => wp_vmovq fun s4 u4 =>
    wp_vbin128 fun s5 u5 => wp_movImm fun s6 u6 => wp_vmovq fun s7 u7 => wp_movImm fun s8 u8 =>
    wp_vmovq fun s9 u9 => wp_vbin128 fun s10 u10 => wp_vinsert1 fun s11 u11 => k s11 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [u11.val 0 (by decide), itT rfl, u10.other r hr0 0 (by decide), u9.other r hr1 0 (by decide), u8.lane,
      u7.other r hr0 0 (by decide), u6.lane, u5.val 0 (by decide), itT rfl, u4.val 0 (by decide), itT rfl,
      u4.other r hr0 0 (by decide), u3.lane, u2.val 0 (by decide), itT rfl, u3.gpr, u1.gpr]
    simp only [XBinOp.eval, VBinOp.sse, qword_zero_app]
  · rw [u11.val 1 (by decide), itF (by decide), u10.val 0 (by decide), itT rfl, u9.val 0 (by decide), itT rfl,
      u9.other _ (by decide) 0 (by decide), u8.lane, u7.val 0 (by decide), itT rfl, u8.gpr, u6.gpr]
    simp only [XBinOp.eval, VBinOp.sse, qword_zero_app]
  · intro x h1 h2 h3 l hl
    rw [u11.other x h1 l hl, u10.other x h2 l hl, u9.other x h3 l hl, u8.lane, u7.other x h2 l hl, u6.lane,
      u5.other x h1 l hl, u4.other x h2 l hl, u3.lane, u2.other x h1 l hl, u1.lane]
  · intro g hg
    rw [u11.gpr, u10.gpr, u9.gpr, u8.other g hg, u7.gpr, u6.other g hg, u5.gpr, u4.gpr, u3.other g hg, u2.gpr,
      u1.other g hg]
  · rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- The constants in `ymm8` to `ymm12`. -/
structure DC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = S4.shuf l
  c9 : ∀ l < 2, s.lane .xmm9 l = shV
  c10 : ∀ l < 2, s.lane .xmm10 l = maskV
  c11 : ∀ l < 2, s.lane .xmm11 l = qV4
  c12 : ∀ l < 2, s.lane .xmm12 l = shuf' l

/-- `yconst r v`: each doubleword of `ymm r` is `v`. -/
theorem yconst_ok' (r : XReg) (v : BitVec 32) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ l < 2, s'.lane r l = ofDwords v v v v) →
      (∀ x, x ≠ r → ∀ l < 2, s'.lane x l = s.lane x l) →
      (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (yconst r v ++ is)) s Q := by
  simp only [yconst, List.cons_append, List.nil_append]
  refine wp_mov32i fun s1 u1 => wp_vmovq fun s2 u2 => wp_vpbcastd' fun s3 u3 => k s3 (fun l hl => ?_)
    (fun x hx l hl => ?_) (fun g hg => ?_) ?_ ?_ ?_
  · rw [u3.val l hl]
    have e : dword (s2.xmm r) 0 = v := by
      rw [show s2.xmm r = s2.lane r 0 from rfl, u2.val 0 (by decide), itT rfl, u1.gpr]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
      simp [hi, show i < 64 by omega]
    simp only [e]
  · rw [u3.other x hx l hl, u2.other x hx l hl, u1.lane]
  · rw [u3.gpr, u2.gpr, u1.other g hg]
  · rw [u3.mem, u2.mem, u1.mem]
  · rw [u3.rd, u2.rd, u1.rd]
  · rw [u3.wr, u2.wr, u1.wr]

theorem consts_ok {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', DC s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (d12Consts ++ is)) s Q := by
  simp only [d12Consts, List.append_assoc, List.cons_append, List.nil_append]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    wp_movImm fun s3 u3 => wp_vmovq fun s4 u4 => wp_vpbcastq fun s5 u5 =>
    yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 => yconst_ok' _ _ fun s7 a7 o7 g7 m7 r7 w7 =>
    k s7 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, u5.other _ (by decide) l hl, u4.other _ (by decide) l hl,
      u3.lane, o2 _ (by decide) (by decide) (by decide) l hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [a1]; rfl
    · rw [b1]; rfl
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, u5.val l hl]
    have e : s4.xmm .xmm9 = (0 : BitVec 64) ++ 0x0000000400000000#64 := by
      rw [show s4.xmm .xmm9 = s4.lane .xmm9 0 from rfl, u4.val 0 (by decide), itT rfl, u3.gpr]; rfl
    rw [e, qword_zero_app]; rfl
  · rw [o7 _ (by decide) l hl, a6 l hl]; rfl
  · rw [a7 l hl]; rfl
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, u5.other _ (by decide) l hl, u4.other _ (by decide) l hl,
      u3.lane]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [a2]; rfl
    · rw [b2]; rfl
  · rw [g7 g hg, g6 g hg, u5.gpr, u4.gpr, u3.other g hg, g2 g hg, g1 g hg]
  · rw [m7, m6, u5.mem, u4.mem, u3.mem, m2, m1]
  · rw [r7, r6, u5.rd, u4.rd, u3.rd, r2, r1]
  · rw [w7, w6, u5.wr, u4.wr, u3.wr, w2, w1]

theorem DC.lupd {s s' : State} (h : DC s) {d : XReg} {v : Nat → BitVec 128} (hu : LUpd s s' d v)
    (hd : d = .xmm0 ∨ d = .xmm1) : DC s' := by
  have e : ∀ r, r = XReg.xmm8 ∨ r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11 ∨ r = .xmm12 →
      ∀ l < 2, s'.lane r l = s.lane r l := fun r hr l hl => hu.other r (by
    rcases hd with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) l hl
  exact ⟨fun l hl => by rw [e _ (by simp) l hl, h.c8 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c9 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c10 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c11 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c12 l hl]⟩

theorem DC.gupd {s s' : State} (h : DC s) (hl : ∀ x l, s'.lane x l = s.lane x l) : DC s' :=
  ⟨fun l h' => by rw [hl, h.c8 l h'], fun l h' => by rw [hl, h.c9 l h'], fun l h' => by rw [hl, h.c10 l h'],
    fun l h' => by rw [hl, h.c11 l h'], fun l h' => by rw [hl, h.c12 l h']⟩

/-! ## A group -/

/-- `x` reduced modulo `q`: `x - q`, plus `q` if that is negative. -/
abbrev red (x : BitVec 32) : BitVec 32 := cadd32 (x - 3329#32)

theorem red_val {c : Nat} (hc : c < 4096) : (red (BitVec.ofNat 32 c)).toNat = (ofNat c : Zq).val := by
  rw [red, cadd32_toNat, val_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, q_eq]
  split <;> omega

/-- The values of lane `l` of a group of the 16 bytes `L`, with the `vpshufb` mask `M`. -/
abbrev vals (L M : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb L M) shV) maskV

theorem dword_red (C : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .paddd (XBinOp.eval .psubd C qV4)
      (XBinOp.eval .pand (XShiftOp.eval .psrad (XBinOp.eval .psubd C qV4) 31) qV4)) j = red (dword C j) := by
  rw [dword_paddd _ _ hj, dword_pand, dword_psrad31 _ hj, dword_psubd _ _ hj, dword_qV4 hj]; rfl

/-- A group: the eight values of the 16 bytes at `rdi` that the masks `M` select, reduced, stored to `rsi`. -/
theorem body_ok {m : XReg} {M : Nat → BitVec 128} {is : List Instr} {s : State} {Q : State → Prop}
    (hm : ∀ l < 2, s.lane m l = M l) (hm0 : m ≠ .xmm0) (hm1 : m ≠ .xmm1) (hc : DC s)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16) (hout : InRegions s.wr (s.gpr .rsi) 32)
    (k : ∀ s', DC s' → (∀ l < 2, s'.lane m l = M l) → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rsi) V ∧ ∀ i < 8,
        V.extractLsb' (32 * i) 32 = red (dword (vals (s.mem.readW (s.gpr .rdi) 128) (M (i / 4))) (i % 4))) →
      WP isa (.block is) s' Q) :
    WP isa (.block (d12Body m ++ is)) s Q := by
  simp only [d12Body, yb, List.cons_append, List.nil_append]
  refine wp_vbcast128 (a := s.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine wp_vbin fun s2 u2 => wp_vvar fun s3 u3 => wp_vbin fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vsh fun s6 u6 => wp_vbin fun s7 u7 => wp_vbin fun s8 u8 => ?_
  refine wp_vst256 (a := s8.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) (by
      rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr,
        u2.gpr, u1.gpr]; exact hout) fun s9 g9 l9 m9 r9 w9 => ?_
  have c1 := hc.lupd u1 (.inl rfl)
  have c2 := c1.lupd u2 (.inl rfl)
  have c3 := c2.lupd u3 (.inl rfl)
  have c4 := c3.lupd u4 (.inl rfl)
  have c5 := c4.lupd u5 (.inl rfl)
  have c6 := c5.lupd u6 (.inr rfl)
  have c7 := c6.lupd u7 (.inr rfl)
  have c8 := c7.lupd u8 (.inl rfl)
  have hg : s8.gpr = s.gpr := by rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  generalize hL : s.mem.readW (s.gpr .rdi) 128 = L at u1
  have h5 : ∀ l < 2, s5.lane .xmm0 l = XBinOp.eval .psubd (vals L (M l)) qV4 := fun l hl => by
    rw [u5.val l hl, u4.val l hl, u3.val l hl, u2.val l hl, u1.val l hl,
      u1.other m hm0 l hl, hm l hl, c2.c9 l hl, c3.c10 l hl, c4.c11 l hl]; rfl
  have h8 : ∀ l < 2, s8.lane .xmm0 l = XBinOp.eval .paddd (XBinOp.eval .psubd (vals L (M l)) qV4)
      (XBinOp.eval .pand (XShiftOp.eval .psrad (XBinOp.eval .psubd (vals L (M l)) qV4) 31) qV4) := fun l hl => by
    rw [u8.val l hl, u7.other .xmm0 (by decide) l hl, u7.val l hl, u6.other .xmm0 (by decide) l hl, u6.val l hl,
      h5 l hl, c6.c11 l hl]; rfl
  refine k s9 (c8.gupd l9) (fun l hl => ?_) (by rw [g9, hg]) (by rw [r9, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd,
    u2.rd, u1.rd]) (by rw [w9, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]) ⟨s8.ymm .xmm0, ?_, ?_⟩
  · rw [l9, u8.other m hm0 l hl, u7.other m hm1 l hl, u6.other m hm1 l hl, u5.other m hm0 l hl,
      u4.other m hm0 l hl, u3.other m hm0 l hl, u2.other m hm0 l hl, u1.other m hm0 l hl, hm l hl]
  · rw [m9, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, congrFun hg .rsi]
  · intro i hi
    rw [State.ymm_eq, ext_app2 _ _ hi]
    by_cases h4 : i < 4
    · rw [itT h4, h8 0 (by decide), dword_red _ (by omega), show i / 4 = 0 by omega, hL]
    · rw [itF h4, h8 1 (by decide), dword_red _ (by omega), show i / 4 = 1 by omega, hL]

/-! ## The values of a group -/

/-- Value `e < 8` of group `g < 32` of `B`, whose bytes `bf` are, reduced, is coefficient `8 g + e` of
`ByteDecode₁₂(B)`. -/
theorem group_val {B : List Byte} (hB : B.length = 384) {g : Nat} (hg : g < 32) {bf : Nat → Byte}
    (hbf : ∀ t < 12, bf t = B.getD (12 * g + t) 0) {e : Nat} (he : e < 8) :
    (red (BitVec.ofNat 32 (candN (fun t => (bf t).toNat) e))).toNat = ((decode12 B)[8 * g + e]!).val := by
  rw [red_val (candN_lt _ (fun t => (bf t).isLt) e)]
  have hcb : cb e = 3 * (e / 2) + e % 2 := rfl
  have h0 := hbf (cb e) (by omega)
  have h1 := hbf (cb e + 1) (by omega)
  unfold candN
  dsimp only
  split
  · rw [show 8 * g + e = 2 * (4 * g + e / 2) by omega, decode12_even B hB (by omega), h0, h1,
      show 12 * g + cb e = 3 * (4 * g + e / 2) by omega, show 12 * g + (cb e + 1) = 3 * (4 * g + e / 2) + 1 by omega]
  · rw [show 8 * g + e = 2 * (4 * g + e / 2) + 1 by omega, decode12_odd B hB (by omega), h0, h1,
      show 12 * g + cb e = 3 * (4 * g + e / 2) + 1 by omega,
      show 12 * g + (cb e + 1) = 3 * (4 * g + e / 2) + 2 by omega]

/-- Coefficient `k` after a write of eight doublewords `V` at coefficient `8 g`. -/
theorem coeffAt_write8 (m : Mem) (p : Addr) (V : BitVec 256) {g k : Nat} (hg : g < 32) (hk : k < 256) :
    coeffAt (m.writeW (coeffAddr p (8 * g)) V) p k =
      if 8 * g ≤ k ∧ k < 8 * g + 8 then V.extractLsb' (32 * (k - 8 * g)) 32 else coeffAt m p k := by
  rw [coeffAt_eq]
  split
  · have e := readW_writeW_inside m (coeffAddr p (8 * g)) V (k := 4 * (k - 8 * g)) (n := 4) (by omega)
      (by decide)
    rw [coeffAddr, Offset.add_add, show 4 * (8 * g) + 4 * (k - 8 * g) = 4 * k by omega] at e
    rw [e, show 8 * (4 * (k - 8 * g)) = 32 * (k - 8 * g) by omega]
  · exact readW_writeW_off m p V (d := 4 * k) (e := 4 * (8 * g)) (n := 4) (by omega) (by omega) (by omega)

/-! ## The loop -/

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
abbrev BB : List Byte := bytesAt s₀.mem (bP s₀) 384
end

/-- After `i` groups. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (12 * i)
  rsi : s.gpr .rsi = coeffAddr (fP s₀) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dc : DC s
  frame : Frame [pR (fP s₀)] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem (fP s₀) k).toNat = ((decode12 (BB s₀))[k]!).val

section
variable {s₀ : State} (hp : decode12K.pre s₀)
include hp

theorem regs : s₀.rd ++ s₀.wr = [⟨bP s₀, 384⟩, pR (fP s₀)] := by rw [hp.1, hp.2.1]; rfl

/-- A group `g`, read 16 bytes from `bP + o` with the masks `M`, whose values are those of bytes `12 g` to
`12 g + 11`, stored to `fP + 32 g`. -/
theorem group {g o : Nat} (hg : g < 32) (ho : o + 16 ≤ 384) {m : XReg} {M : Nat → BitVec 128} {is : List Instr}
    {s : State} {Q : State → Prop} (hm : ∀ l < 2, s.lane m l = M l) (hm0 : m ≠ .xmm0) (hm1 : m ≠ .xmm1)
    (hM : ∀ L : BitVec 128, ∀ e < 8, (∀ t < 16, byte L t = s₀.mem (bP s₀ + BitVec.ofNat 64 (o + t))) →
      ∃ bf : Nat → Byte, (∀ t < 12, bf t = (BB s₀).getD (12 * g + t) 0) ∧
        dword (vals L (M (e / 4))) (e % 4) = BitVec.ofNat 32 (candN (fun t => (bf t).toNat) e))
    (hdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 o) (hsi : s.gpr .rsi = coeffAddr (fP s₀) (8 * g))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hc : DC s) (hf : Frame [pR (fP s₀)] s₀.mem s.mem)
    (hd : ∀ k < 8 * g, (coeffAt s.mem (fP s₀) k).toNat = ((decode12 (BB s₀))[k]!).val)
    (k : ∀ s', DC s' → (∀ l < 2, s'.lane m l = M l) → s'.gpr = s.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr →
      Frame [pR (fP s₀)] s₀.mem s'.mem →
      (∀ k < 8 * (g + 1), (coeffAt s'.mem (fP s₀) k).toNat = ((decode12 (BB s₀))[k]!).val) →
      WP isa (.block is) s' Q) :
    WP isa (.block (d12Body m ++ is)) s Q := by
  have hrw : s.rd ++ s.wr = [⟨bP s₀, 384⟩, pR (fP s₀)] := by rw [hrd, hwr, regs hp]
  refine body_ok hm hm0 hm1 hc (by rw [hrw, hdi]; exact ⟨_, by simp, Offset.contains_base _ ho (by omega)⟩)
    (by rw [hwr, hp.2.1, hsi]; exact ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (show 4 * (8 * g) + 32 ≤ 1024 by omega) (by omega)⟩)
    fun s' hc' hm' hg' hrd' hwr' ⟨V, hmem, hV⟩ => k s' hc' hm' hg' (by rw [hrd', hrd]) (by rw [hwr', hwr]) ?_ ?_
  · rw [hmem, hsi]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 4 * (8 * g) + 256 / 8 ≤ 1024 by omega) (by omega))
  · intro c hc
    have hL : ∀ t < 16, byte (s.mem.readW (s.gpr .rdi) 128) t = s₀.mem (bP s₀ + BitVec.ofNat 64 (o + t)) :=
      fun t ht => by
        rw [byte, byte_readW _ _ (by omega), hdi, Offset.add_add]
        exact bytes_frame hf (by simpa using hp.2.2.1) (by decide) _ (by omega)
    rw [hmem, hsi, coeffAt_write8 _ _ _ hg (by omega)]
    split
    · rename_i hin
      obtain ⟨bf, hbf, hv⟩ := hM _ (c - 8 * g) (by omega) hL
      rw [hV _ (by omega), hv, group_val (bytesAt_length _ _ _) hg hbf (by omega),
        show 8 * g + (c - 8 * g) = c by omega]
    · exact hd c (by omega)

omit hp in
theorem hM_mid {g : Nat} (hg : g < 31) : ∀ L : BitVec 128, ∀ e < 8,
    (∀ t < 16, byte L t = s₀.mem (bP s₀ + BitVec.ofNat 64 (12 * g + t))) →
    ∃ bf : Nat → Byte, (∀ t < 12, bf t = (BB s₀).getD (12 * g + t) 0) ∧
      dword (vals L (S4.shuf (e / 4))) (e % 4) = BitVec.ofNat 32 (candN (fun t => (bf t).toNat) e) :=
  fun L e he hL => ⟨fun t => byte L t, fun t ht => by dsimp only; rw [hL t (by omega), bytesAt_getD _ _ (by omega)], by
    have := cand_dword L (show e / 4 < 2 by omega) (show e % 4 < 4 by omega)
    rwa [show 4 * (e / 4) + e % 4 = e by omega] at this⟩

omit hp in
theorem hM_last : ∀ L : BitVec 128, ∀ e < 8,
    (∀ t < 16, byte L t = s₀.mem (bP s₀ + BitVec.ofNat 64 (368 + t))) →
    ∃ bf : Nat → Byte, (∀ t < 12, bf t = (BB s₀).getD (12 * 31 + t) 0) ∧
      dword (vals L (shuf' (e / 4))) (e % 4) = BitVec.ofNat 32 (candN (fun t => (bf t).toNat) e) :=
  fun L e he hL => ⟨fun t => byte L (4 + t), fun t ht => by
    dsimp only; rw [hL (4 + t) (by omega), bytesAt_getD _ _ (by omega), show 368 + (4 + t) = 12 * 31 + t by omega], by
    have := cand_dword' L (show e / 4 < 2 by omega) (show e % 4 < 4 by omega)
    rwa [show 4 * (e / 4) + e % 4 = e by omega] at this⟩

theorem step {i : Nat} (hi : i < 31) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (d12Body .xmm8 ++ d12Step)) s fun s' => Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine group hp (g := i) (o := 12 * i) (by omega) (by omega) hI.dc.c8 (by decide) (by decide) (hM_mid hi)
    hI.rdi hI.rsi hI.rd hI.wr hI.dc hI.frame hI.done fun s1 hc1 _ hg1 hrd1 hwr1 hf1 hd1 => ?_
  simp only [d12Step]
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have c4 := (hc1.gupd u2.lane).gupd u3.lane |>.gupd u4.lane
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, hrd1], by rw [u4.wr, u3.wr, u2.wr, hwr1], c4,
    by rw [u4.mem, u3.mem, u2.mem]; exact hf1, fun k hk => by rw [u4.mem, u3.mem, u2.mem]; exact hd1 k hk⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1, hI.rdi,
      show BitVec.signExtend 64 (12 : BitVec 32) = BitVec.ofNat 64 12 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 12 * i + 12 = 12 * (i + 1) by omega]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1, hI.rsi, coeffAddr, coeffAddr,
      show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 4 * (8 * i) + 32 = 4 * (8 * (i + 1)) by omega]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), hg1]; rfl

theorem main : WP isa decode12Avx2 s₀ fun s => Frame [pR (fP s₀)] s₀.mem s.mem ∧
    ∀ k < 256, (coeffAt s.mem (fP s₀) k).toNat = ((decode12 (BB s₀))[k]!).val := by
  unfold decode12Avx2
  refine WP.seq (consts_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 31) (by decide) (by decide) (Inv s₀)
    (fun i hi s hI _ => step hp hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1], by rw [u2.wr, hw1],
      hc1.gupd u2.lane, by rw [u2.mem, hm1]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩
    (by rw [u2.gpr]; rfl))
  · refine wp_subi' fun s3 u3 _ => group hp (g := 31) (o := 368) (by decide) (by decide)
      (fun l hl => by rw [u3.lane, hI.dc.c12 l hl]) (by decide) (by decide) hM_last ?_
      (by rw [u3.other _ (by decide), hI.rsi]) (by rw [u3.rd, hI.rd]) (by rw [u3.wr, hI.wr]) (hI.dc.gupd u3.lane)
      (by rw [u3.mem]; exact hI.frame) (fun k hk => by rw [u3.mem]; exact hI.done k hk)
      fun s4 _ _ _ _ _ hf4 hd4 => wp_vzu fun s5 _ hm5 _ _ => WP.block_nil ⟨by rw [hm5]; exact hf4,
        fun k hk => by rw [hm5]; exact hd4 k hk⟩
    rw [u3.gpr, hI.rdi, show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 by decide,
      Offset.add_ofNat_sub _ (by decide)]
  · rw [u2.other _ (by decide), hg1 _ (by decide)]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide)]; simp

theorem correct : ∃ t s', Exec isa decode12Avx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ decode12K.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hf, hd⟩, hk⟩ := WP.keep (c := decode12Avx2) [.rax, .rdi, .rsi, .rcx] (main hp)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hp.2.2.2.2)), polyIs_of_toNat hd⟩

end

end VG.Proof.MlKem.X86_64.D12Y

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem decode12Y_correct (s : State) (hs : decode12K.pre s) :
    ∃ t s', Exec isa decode12Avx2 s t s' ∧ abiPreserved s s' ∧ decode12K.post s s' :=
  D12Y.correct hs

theorem decode12Y_ct : ConstantTime isa decode12K.pre decode12K.pub decode12Avx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem decode12Y_verified :
    Verified X86_64.target decode12Avx2 (Spec.MlKem.decode12Contract X86_64.abi) :=
  Verified.of_correct decode12Y_correct decode12Y_ct (by
    mlkem_implies [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, decode12K, X86_64.abi,
      X86_64.argRegs] [decode12Sat] using decode12Sat)

end VG.Proof.MlKem.X86_64
