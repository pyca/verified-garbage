module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # A message of one hash value's length, hashed by the compression function

Parameter generation hashes seeds of `N` bytes, as many as the hash value
has (SHA-1's 20, SHA-256's 32): one block, the seed and its padding, after
the initial value, compressed once by a verified compression function. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Pbkdf2.Md.X86 (Hash storeW)
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Md.X86 (MdOk CmpArgs storeW_ok cmp_ok OutOk inReg)
open VG.X86.Wp (Upd wp_mov wp_addi)
open VG.Proof.Pbkdf2.Stream.X86 (stk After setWidth_add toNat_add_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_sep)
open VG.WriteBytes (writeBytes writeBytes_frame)

/-- What hashing needs of a hash function's code and its initial value:
the proofs' facts about the code (`MdOk`), an initial value whose bytes
are the `md`'s initial hash value, a length field of eight bytes,
big-endian, and a digest of the hash value's length. -/
structure HashOk (H : Hash) (iv : List (BitVec 32)) where
  ok : MdOk H
  ivLen : 4 * iv.length = H.N
  ivVal : ∀ m p, Spec.Sha256.bytesAt m p H.N = ivBytes iv → ok.md.stateAt m p = ok.iv
  lenB : ok.md.lenBytes H.N = (List.range 8).map fun i => BitVec.ofNat 8 ((8 * H.N) >>> (8 * (7 - i)))
  B : H.B = 64
  L : H.L = 8
  DN : H.D = H.N

theorem ivBytes_length (iv : List (BitVec 32)) : (ivBytes iv).length = 4 * iv.length := by
  induction iv with
  | nil => rfl
  | cons _ _ ih =>
    simp only [ivBytes, List.flatMap_cons, List.length_append, List.length_map, List.length_range,
      List.length_cons] at ih ⊢
    omega

theorem padBytes_length {n : Nat} (h : n + 9 ≤ 64) : (padBytes n).length = 64 - n := by
  simp only [padBytes, List.length_append, List.length_singleton, List.length_replicate, List.length_map,
    List.length_range]
  omega

/-- `d := edi + o`. -/
theorem scr_ok {d : Reg} {o : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr d = s.gpr .edi + BitVec.ofNat 32 o → (∀ r, r ≠ d → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (scr d o ++ is)) s Q := by
  simp only [scr, List.cons_append, List.nil_append]
  exact wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => k s₂ (by rw [u₂.gpr, u₁.gpr])
    (fun r hr => by rw [u₂.other r hr, u₁.other r hr]) (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) (by rw [u₂.syms, u₁.syms])

/-- `edi + d`, widened: the address `d` bytes into the working space. -/
theorem Scr.wide {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d < size) :
    (s.gpr .edi + BitVec.ofNat 32 d).setWidth 64 = off base d :=
  hs.ea hd

theorem Scr.toNat_add {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d < size) :
    (s.gpr .edi + BitVec.ofNat 32 d).toNat = base.toNat + d := by
  have := hs.nowrap; have := hs.edi_toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), hs.edi_toNat,
    Nat.mod_eq_of_lt (by omega)]

/-- A part of the working space is within the writable regions. -/
theorem Scr.covers {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) : Covers [⟨off base d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs.wr, d, rfl, h⟩

theorem contains_start (p : Addr) {n k : Nat} (h : n ≤ k) : (⟨p, k⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The three writes of a hash, within its regions. -/
theorem frame_join {A B C D A' : Region} {m₁ m₂ m₃ m₄ : Mem} (f₁ : Frame [A] m₁ m₂)
    (f₂ : Frame ([A', B] ++ [D]) m₂ m₃) (f₃ : Frame [C] m₃ m₄) (h : Region.Sub A' A) :
    Frame [A, B, C, D] m₁ m₄ := by
  refine (f₁.mono ?_).trans ((f₂.sub ?_).trans (f₃.mono ?_))
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact .head _
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨A, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), fun _ h => h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), fun _ h => h⟩
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact .tail _ (.tail _ (.head _))

section
variable {H : Hash} {iv : List (BitVec 32)} (F : HashOk H iv)
include F

theorem HashOk.N_le : H.N + 12 ≤ 64 := by
  have := F.ok.sizes.DL; have := F.B; have := F.L; have := F.DN; omega

theorem HashOk.N4 : H.N % 4 = 0 := by
  have := F.ok.sizes.N; omega

/-- The block before the compression: the initial value, the padding after
the message, the block's address in `eax` and the scratch space's in `ebp`. -/
theorem prep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsz : sHScr ≤ size) {Q : State → Prop}
    (k : ∀ t, t.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 sState →
      t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sState + BitVec.ofNat 32 H.N →
      t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 sHScr →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .ebp → t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.mem = writeBytes (writeBytes s.mem (off base sState) (ivBytes iv))
        (off base sState + BitVec.ofNat 64 (H.N + H.N)) (padBytes H.N) → Q t) :
    WP isa (.block (scr .ebx sState ++ ivStore iv ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (H.N + H.N) (padBytes H.N) ((64 - H.N) / 4) ++
      [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 H.N))] ++ scr .ebp sHScr)) s Q := by
  have nl := F.N_le; have n4 := F.N4; have ivl := F.ivLen
  have nw := hs.nowrap
  have hsn : sState + H.N + 64 ≤ sHScr := by simp only [sState, sHScr]; omega
  have yNat := Scr.toNat_add hs (d := sState) (by simp only [sState, sHScr] at hsz ⊢; omega)
  have yW := Scr.wide hs (d := sState) (by simp only [sState, sHScr] at hsz ⊢; omega)
  simp only [List.append_assoc]
  refine scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => ?_
  have cov : ∀ d n, sState ≤ d → d + n ≤ sState + H.N + 64 →
      ∀ j, j + 4 ≤ n → InRegions s₁.wr (addr (s.gpr .edi + BitVec.ofNat 32 sState) (d - sState + j)) 4 := by
    intro d n h₁ h₂ j hj
    rw [addr_eq (by omega), yW, Offset.add_add, wr₁]
    exact hs.write (d := sState + (d - sState + j)) (n := 4) (by omega)
  unfold ivStore
  refine storeW_ok (by decide) iv.length _ s₁ _ (by rw [ivBytes_length]) e₁ (by omega)
    (fun j hj => by simpa using cov sState (4 * iv.length) (Nat.le_refl _) (by omega) (4 * j) (by omega))
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine storeW_ok (by decide) ((64 - H.N) / 4) _ s₂ _ (by rw [padBytes_length (by omega)]; omega)
    (by rw [g₂ _ (by decide), e₁]) (by omega)
    (fun j hj => by
      rw [wr₂]
      have := cov (sState + (H.N + H.N)) (64 - H.N) (by omega) (by omega) (4 * j) (by omega)
      rwa [show sState + (H.N + H.N) - sState + 4 * j = H.N + H.N + 4 * j by omega] at this)
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  refine scr_ok fun s₆ e₆ g₆ m₆ rd₆ wr₆ _ => WP.block_nil (k s₆ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      g₂ _ (by decide), e₁]
  · rw [g₆ _ (by decide), u₅.gpr, u₄.gpr, g₃ _ (by decide), g₂ _ (by decide), e₁]
  · rw [e₆, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide)]
  · intro r a b c d
    rw [g₆ r d, u₅.other r a, u₄.other r a, g₃ r c, g₂ r c, g₁ r b]
  · rw [rd₆, u₅.rd, u₄.rd, rd₃, rd₂, rd₁]
  · rw [wr₆, u₅.wr, u₄.wr, wr₃, wr₂, wr₁]
  · rw [m₆, u₅.mem, u₄.mem, m₃, m₂, m₁, yW, Nat.mul_comm 4 ((64 - H.N) / 4),
      Nat.div_mul_cancel (by omega), ← ivBytes_length,
      List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (by rw [padBytes_length (by omega)]),
      BitVec.add_zero]

/-- The bytes of the block after the hash value: the message, then the
padding. -/
theorem block_bytes {m : Mem} {Y : Addr} {k : Nat} (hk : k < 64) :
    writeBytes (writeBytes m Y (ivBytes iv)) (Y + BitVec.ofNat 64 (H.N + H.N)) (padBytes H.N)
        (Y + BitVec.ofNat 64 H.N + BitVec.ofNat 64 k) =
      (Spec.Sha256.bytesAt m (Y + BitVec.ofNat 64 H.N) H.N ++ padBytes H.N).getD k 0 := by
  have nl := F.N_le; have ivl := F.ivLen
  have pl := padBytes_length (n := H.N) (by omega)
  have il := ivBytes_length iv
  have ml : (Spec.Sha256.bytesAt m (Y + BitVec.ofNat 64 H.N) H.N).length = H.N := by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]
  rw [Offset.add_add]
  have d1 := Offset.sub_toNat' Y (d := H.N + H.N) (e := H.N + k) (by omega) (by omega)
  have d2 := Mem.sub_ofNat_toNat Y (show H.N + k < 2 ^ 64 by omega)
  simp only [writeBytes, d1, d2, List.getD_eq_getElem?_getD]
  by_cases hN : H.N ≤ k
  · have c1 : H.N + H.N ≤ H.N + k := by omega
    have c2 : H.N + k - (H.N + H.N) < (padBytes H.N).length := by rw [pl]; omega
    simp only [c1, ↓reduceIte, c2]
    rw [List.getElem?_append_right (by rw [ml]; exact hN), ml]
    congr 2
    omega
  · have c1 : ¬ H.N + H.N ≤ H.N + k := by omega
    have c2 : ¬ 2 ^ 64 + (H.N + k) - (H.N + H.N) < (padBytes H.N).length := by rw [pl]; omega
    have c3 : ¬ H.N + k < (ivBytes iv).length := by rw [il]; omega
    simp only [c1, ↓reduceIte, c2, c3]
    rw [List.getElem?_append_left (by rw [ml]; omega)]
    simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show k < H.N by omega),
      Option.map_some, Option.getD_some]
    rw [Offset.add_add]

theorem hash_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {dst : Nat} (hsz : sHScr + H.so ≤ size) (hsC : sHScr < size) (hdst : dst + H.N ≤ size)
    (hsepS : sState + H.N + 64 ≤ dst ∨ dst + H.N ≤ sState)
    (hsepC : dst + H.N ≤ sHScr ∨ sHScr + H.so ≤ dst)
    (h48 : 48 ≤ (s.gpr .esp).toNat) (hstk : (stk s).Disjoint ⟨base, size⟩) :
    WP isa (Impl.Dsa.X86.Generation.hash H iv H.N dst) s fun t =>
      Spec.Sha256.bytesAt t.mem (off base dst) H.N =
        F.ok.hH.SH.H.hash (Spec.Sha256.bytesAt s.mem (off base (sState + H.N)) H.N) ∧
      Frame [⟨off base sState, H.N + 64⟩, ⟨off base sHScr, H.so⟩, ⟨off base dst, H.N⟩, stk s] s.mem t.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have nl := F.N_le; have n4 := F.N4; have ivl := F.ivLen
  have hB := F.B; have hL := F.L; have hD := F.DN
  have nw := hs.nowrap
  have hso : sState + H.N + 64 ≤ sHScr := by simp only [sState, sHScr]; omega
  have hsS : sState < size := by simp only [sState, sHScr] at hsz hso ⊢; omega
  let Y := off base sState
  have yNat := Scr.toNat_add hs hsS
  have yW := Scr.wide hs hsS
  have cNat := Scr.toNat_add hs hsC
  have cW := Scr.wide hs hsC
  unfold Impl.Dsa.X86.Generation.hash
  simp only [seqs]
  refine WP.seq (prep_ok F hs (by omega) fun t eb ea ep g rd wr m => ?_)
  have tsp : t.gpr .esp = s.gpr .esp := g _ (by decide) (by decide) (by decide) (by decide)
  have tdi : t.gpr .edi = s.gpr .edi := g _ (by decide) (by decide) (by decide) (by decide)
  have cargs : CmpArgs H.N H.B H.so t (s.gpr .edi + BitVec.ofNat 32 sState) (s.gpr .edi + BitVec.ofNat 32 sHScr) :=
    { ebx := eb, eax := ea, ebp := ep, sp48 := by rw [tsp]; exact h48
      cst := by rw [yW, wr]; exact Scr.covers hs (by rw [hB]; omega)
      csc := by rw [cW, wr]; exact Scr.covers hs (by omega)
      st_sc := by rw [yW, cW]; exact Offset.disjoint base (by rw [hB]; omega) (by omega) (by omega)
      b_st := by
        rw [stk, tsp, yW]
        exact hstk.sub_right (Offset.sub_base base (by rw [hB]; omega))
      b_sc := by
        rw [stk, tsp, cW]
        exact hstk.sub_right (Offset.sub_base base (by omega))
      nst := by rw [yNat, hB]; omega
      nsc := by rw [cNat]; omega }
  refine WP.seq (cmp_ok F.ok.comp (by rw [hB]; decide) cargs fun u au cu => ?_)
  rw [yW] at cu
  have udi : u.gpr .edi = s.gpr .edi := (au.cs .edi (by decide)).trans tdi
  have usp : u.gpr .esp = s.gpr .esp := (au.cs .esp (by decide)).trans tsp
  simp only [List.append_assoc]
  refine scr_ok fun v ev gv mv rdv wrv _ => scr_ok fun w ew gw mw rdw wrw _ => ?_
  have npos := F.ok.sizes.N.1
  have hdN : dst < size := by omega
  have wbx : w.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 sState := by
    rw [gw _ (by decide), ev, udi]
  have wax : w.gpr .eax = s.gpr .edi + BitVec.ofNat 32 dst := by
    rw [ew, gv _ (by decide), udi]
  have dW := Scr.wide hs hdN
  have dNat := Scr.toNat_add hs hdN
  refine WP.mono (F.ok.out w (by rw [wbx, yNat]; omega) (by rw [wax, dNat]; omega) ?_ ?_ ?_)
    fun x ⟨gx, rdx, wrx, mx⟩ => ?_
  · rw [wbx, yW, rdw, wrw, rdv, wrv, au.rd, au.wr, rd, wr]
    exact hs.read (by omega)
  · rw [wax, dW, wrw, wrv, au.wr, wr]; exact hs.write (by omega)
  · rw [wbx, wax, yW, dW]; exact Offset.disjoint base (by omega) (by omega) (by omega)
  rw [wbx, wax, yW, dW, mw, mv] at mx
  -- The value.
  have msgEq : Spec.Sha256.bytesAt s.mem (off base (sState + H.N)) H.N =
      Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N := by
    simp only [Y, off, Offset.add_add]
  have pl := padBytes_length (n := H.N) (by omega)
  have ivAt : F.ok.md.stateAt t.mem Y = F.ok.iv := by
    apply F.ivVal
    rw [m, bytesAt_writeBytes_sep _ _ (Offset.sep_base Y (by omega) (by omega)) (by omega),
      VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (by rw [ivBytes_length]; omega) (by omega)]
  have blk : F.ok.md.blockAt t.mem (Y + BitVec.ofNat 64 H.N) =
      F.ok.md.parse fun k => (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N ++ padBytes H.N).getD k 0 := by
    simp only [Md.blockAt]
    refine F.ok.md.parse_congr fun k hk => ?_
    rw [m, block_bytes F (by rw [← hB]; exact hk)]
  have ml : (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N).length = H.N := by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]
  have padEq : ∀ msg : List Byte, msg.length = H.N →
      VG.Proof.MdStream.Md.rest H.B msg ++ [0x80] ++ List.replicate (H.B - H.L - 1 - H.N % H.B) 0 ++
        F.ok.md.lenBytes H.N = msg ++ padBytes H.N := by
    intro msg hm
    rw [F.lenB, hB, hL]
    simp only [VG.Proof.MdStream.Md.rest, hm, padBytes, List.append_assoc]
    rw [Nat.div_eq_of_lt (by omega), Nat.mul_zero, List.drop_zero, Nat.mod_eq_of_lt (by omega)]
  have hashEq : F.ok.hH.SH.H.hash (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N) =
      F.ok.md.digest (F.ok.md.compress F.ok.iv
        (F.ok.md.parse fun k => (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N ++ padBytes H.N).getD k 0)) := by
    rw [F.ok.link.hash, Md.hash_one F.ok.md (by rw [hB]; decide) (by rw [ml, hB, hL]; omega), ml,
      Nat.div_eq_of_lt (by rw [hB]; omega), Md.compressList_zero, padEq _ ml, hD,
      List.take_of_length_le (by rw [F.ok.md.digest_length])]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mx, VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (F.ok.md.digest_length _) (by omega), cu, ivAt, blk,
      msgEq, hashEq]
  · have f₁ : Frame [⟨Y, H.N + 64⟩] s.mem t.mem := by
      rw [m]
      exact (writeBytes_frame _ _ _ (by rw [ivBytes_length]; exact contains_start _ (by omega))).trans
        (writeBytes_frame _ _ _ (by rw [pl]; exact Offset.contains_base Y (by omega) (by omega)))
    have f₂ := au.frame
    rw [yW, cW, stk, tsp] at f₂
    have f₃ : Frame [⟨off base dst, H.N⟩] u.mem x.mem := by
      rw [mx]; exact writeBytes_frame _ _ _ (by rw [F.ok.md.digest_length]; exact contains_start _ (by omega))
    have s₂ : Region.Sub ⟨off base sState, H.N⟩ ⟨off base sState, H.N + 64⟩ := Region.sub_prefix (by omega)
    exact frame_join f₁ f₂ f₃ s₂

  · intro r a b c d e
    rw [gx r c d, gw r a, gv r b, au.cs r ?_, g r a b c e]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
    cases r <;> simp_all
  · rw [rdx, rdw, rdv, au.rd, rd]
  · rw [wrx, wrw, wrv, au.wr, wr]

end

end VG.Proof.Dsa.X86.Generation
