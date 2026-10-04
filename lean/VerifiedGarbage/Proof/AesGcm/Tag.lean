import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.TagScratch

/-!
# AES-GCM's tags passed through their working space

`vg_aes_gcm_stream_finish`, `vg_aes_gcm_stream_verify`, `vg_aes_gcm_seal`
and `vg_aes_gcm_open` take a 16-byte `tag`; their code is proved for
functions whose parameter there is `work: *mut [u64; 320]`, working space
that carries the tag in its first 16 bytes (`streamFinishWorkContract`, …,
on `Sig.tagWork`), and each target's frame (`Verified.tagScratch`) copies
the tag into working space on its stack and back.

`streamFinish_tagFrame`, … relate the two contracts (`Sig.TagFrame`): the
key context, the state, the nonce, the additional data and the data are the
function's buffers, which the code's memory agrees with on entry; the tag
the code computes is in the first 16 bytes of `work`, which the frame copies
to `tag`; and a received tag of `tag_len` bytes is in the first `tag_len`
bytes of both when `tag_len` is a length §5.2.1.2 allows (at most 16), and
rejected by both otherwise, whatever their bytes.
-/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-! ## The contracts with working space in the tag's place -/

/-- `vg_aes_gcm_stream_finish` with `work: *mut [u64; 320]` in place of
`tag`. -/
def streamFinishWorkSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("work", .array true .u64 320)]

def streamFinishWorkPre (pb : Nat) : Curry (streamFinishWorkSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _state _aadLen _textLen _work _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- `streamFinishPost`, with the tag in the first 16 bytes of `work`. -/
def streamFinishWorkPost (pb : Nat) : streamFinishWorkSig.Post pb :=
  fun ctx rounds state aadLen textLen work m m' _ =>
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a c, StreamRepr m state ciph h iv a c →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
      Spec.Aes.bytesAt m' work 16 = fullTag ciph h iv a c

def streamFinishWorkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishWorkSig.contract A (pre := streamFinishWorkPre A.ptrBits)
    (post := streamFinishWorkPost A.ptrBits) (writeArgs := true) (stack := stack)

theorem streamFinishWorkSig_eq : streamFinishWorkSig = streamFinishSig.tagWork 5 "work" .u64 320 := rfl

/-- `vg_aes_gcm_stream_verify` with `work: *mut [u64; 320]` in place of
`tag`. -/
def streamVerifyWorkSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("work", .array true .u64 320), ("tag_len", .int .usize true)]
  ret := some .u32

def streamVerifyWorkPre (pb : Nat) : Curry (streamVerifyWorkSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _state _aadLen _textLen _work _tagLen _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- `streamVerifyPost`, with the tags in the first bytes of `work`. -/
def streamVerifyWorkPost (pb : Nat) : streamVerifyWorkSig.Post pb :=
  fun ctx rounds state aadLen textLen work tagLen m m' r =>
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a c, StreamRepr m state ciph h iv a c →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tagLen.toNat ∧ t.take tagLen.toNat = Spec.Aes.bytesAt m work tagLen.toNat then
        r = 1 ∧ Spec.Aes.bytesAt m' work 16 = t
      else r = 0 ∧ Spec.Aes.bytesAt m' work 16 = zeros 16

def streamVerifyWorkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyWorkSig.contract A (pre := streamVerifyWorkPre A.ptrBits)
    (post := streamVerifyWorkPost A.ptrBits) (writeArgs := true) (stack := stack)

theorem streamVerifyWorkSig_eq : streamVerifyWorkSig = streamVerifySig.tagWork 5 "work" .u64 320 := rfl

/-- `vg_aes_gcm_seal` with `work: *mut [u64; 320]` in place of `tag`. -/
def sealWorkSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 320)]

def sealWorkPre (pb : Nat) : Curry (sealWorkSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce _nonceLen _aad _aadLen _data _len _work _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- `sealPost`, with the tag in the first 16 bytes of `work`. -/
def sealWorkPost (pb : Nat) : sealWorkSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len work m m' _ =>
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16
        (Spec.Aes.bytesAt m nonce nonceLen.toNat) (Spec.Aes.bytesAt m data len.toNat)
        (Spec.Aes.bytesAt m aad aadLen.toNat) =
      (Spec.Aes.bytesAt m' data len.toNat, Spec.Aes.bytesAt m' work 16)

def sealWorkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealWorkSig.contract A (pre := sealWorkPre A.ptrBits) (post := sealWorkPost A.ptrBits)
    (writeArgs := true) (stack := stack)

theorem sealWorkSig_eq : sealWorkSig = sealSig.tagWork 5 "work" .u64 320 := rfl

/-- `vg_aes_gcm_open` with `work: *mut [u64; 320]` in place of `tag`. -/
def openWorkSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 320),
    ("tag_len", .int .usize true)]
  ret := some .u32

def openWorkPre (pb : Nat) : Curry (openWorkSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce _nonceLen _aad _aadLen _data _len _work _tagLen _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- `openPost`, with the received tag in the first `tag_len` bytes of
`work`. -/
def openWorkPost (pb : Nat) : openWorkSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m m' r =>
    match openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Spec.Aes.bytesAt m nonce nonceLen.toNat) (Spec.Aes.bytesAt m data len.toNat)
        (Spec.Aes.bytesAt m aad aadLen.toNat) (Spec.Aes.bytesAt m work tagLen.toNat) with
    | some pt => r = 1 ∧ Spec.Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Spec.Aes.bytesAt m' data len.toNat = Spec.Aes.bytesAt m data len.toNat

/-- `openLeak`, with the received tag in the first `tag_len` bytes of
`work`. -/
def openWorkLeak (pb : Nat) : Curry (openWorkSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m =>
    [if (openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Spec.Aes.bytesAt m nonce nonceLen.toNat) (Spec.Aes.bytesAt m data len.toNat)
        (Spec.Aes.bytesAt m aad aadLen.toNat) (Spec.Aes.bytesAt m work tagLen.toNat)).isSome
      then 1 else 0]

def openWorkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openWorkSig.contract A (pre := openWorkPre A.ptrBits) (post := openWorkPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openWorkLeak A.ptrBits))

theorem openWorkSig_eq : openWorkSig = openSig.tagWork 5 "work" .u64 320 := rfl

/-! ## The tag frame's obligations -/

/-- The 16 bytes at `t` of `m'` are those at `W` of `m₃`. -/
theorem bytesAt_tagOut {t W : Addr} {m₃ m' : Mem} (h : TagOut t W m₃ m') :
    Spec.Aes.bytesAt m' t 16 = Spec.Aes.bytesAt m₃ W 16 := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h.2 i (List.mem_range.mp hi)

/-- A buffer separate from the tag is the code's on return. -/
theorem bytesAt_tagOut_sep {t W p : Addr} {n : Nat} {m₃ m' : Mem} (h : TagOut t W m₃ m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨t, 16⟩) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m₃ p n :=
  bytesAt_congr fun i hi => h.1 _ fun hc => hd _ (by
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    have := Nat.mod_le i (2 ^ 64)
    by_cases hw : i < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hw]; omega
    · have := (BitVec.ofNat 64 i).isLt
      simp only [BitVec.toNat_ofNat] at this
      omega) hc

/-- The received tag's bytes, if `tag_len` is a length §5.2.1.2 allows. -/
theorem recvTag_eq {t W : Addr} {m₁ m₂ : Mem} {tl : Nat}
    (hW : ∀ i < 16, m₂ (W + BitVec.ofNat 64 i) = m₁ (t + BitVec.ofNat 64 i)) (hok : tagLenOk tl) :
    Spec.Aes.bytesAt m₂ W tl = Spec.Aes.bytesAt m₁ t (min tl 16) := by
  have h16 : tl ≤ 16 := by simp [tagLenOk] at hok; omega
  rw [Nat.min_eq_left h16]
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => hW i (by have := List.mem_range.mp hi; omega)

/-- `streamVerifyPost`'s comparison reads the received tag only for a length
§5.2.1.2 allows. -/
theorem verify_cond {k : Nat} {T tag₁ tag₂ : List Byte} {P Q : Prop} (e : tagLenOk k → tag₁ = tag₂) :
    (if tagLenOk k ∧ T.take k = tag₁ then P else Q) = (if tagLenOk k ∧ T.take k = tag₂ then P else Q) := by
  by_cases hok : tagLenOk k = true
  · rw [e hok]
  · simp only [hok, Bool.false_eq_true, false_and, ↓reduceIte]

theorem streamFinish_tagFrame (pb : Nat) :
    streamFinishSig.TagFrame 5 "work" .u64 320 pb (streamFinishPre pb) (streamFinishPost pb) none
      (streamFinishWorkPre pb) (streamFinishWorkPost pb) none where
  pre := fun
    | [_, _, _, _, _], [], _, _, _, _, _, _, _, h => h
  post := fun
    | [ctx, rd, st, _, _], [], t, W, m₁, m₂, m₃, m', r, _, _, ⟨hag, _⟩, hpre, _, hto, h => by
      simp only [streamFinishSig, List.take, List.drop, Sig.bufs, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hag
      have hc := agree_of hag.1
      have hs := agree_of hag.2
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
        ArgWord.addr] (streamFinishPre pb) _ m₁ at hpre
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
        ArgWord.addr] (streamFinishWorkPost pb) _ m₂ m₃ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
        ArgWord.addr] (streamFinishPost pb) _ m₁ m' r
      dsimp only [List.cons_append, List.nil_append, Curry.apply, streamFinishPre, streamFinishPost,
        streamFinishWorkPost, ArgWord.ofRaw] at hpre h ⊢
      intro iv a c hr hl ht
      have hn := le15 hpre
      have ec := ctxCiph_congr hn fun i hi => hc i (by omega)
      have eh := ctxH_congr fun i hi => hc i (by omega)
      rw [← ec, ← eh] at hr
      rw [bytesAt_tagOut hto, ← ec, ← eh]
      exact h iv a c (streamRepr_congr (fun i hi => hs i (by omega)) hr) hl ht
  leak := trivial

theorem streamVerify_tagFrame (pb : Nat) :
    streamVerifySig.TagFrame 5 "work" .u64 320 pb (streamVerifyPre pb) (streamVerifyPost pb) none
      (streamVerifyWorkPre pb) (streamVerifyWorkPost pb) none where
  pre := fun
    | [_, _, _, _, _], [_], _, _, _, _, _, _, _, h => h
  post := fun
    | [ctx, rd, st, _, _], [tl], t, W, m₁, m₂, m₃, m', r, _, _, ⟨hag, hW⟩, hpre, _, hto, h => by
      simp only [streamVerifySig, List.take, List.drop, Sig.bufs, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hag
      have hc := agree_of hag.1
      have hs := agree_of hag.2
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
        ArgWord.addr, ArgWord.int pb] (streamVerifyPre pb) _ m₁ at hpre
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
        ArgWord.addr, ArgWord.int pb] (streamVerifyWorkPost pb) _ m₂ m₃ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
        ArgWord.addr, ArgWord.int pb] (streamVerifyPost pb) _ m₁ m' r
      dsimp only [List.cons_append, List.nil_append, Curry.apply, streamVerifyPre, streamVerifyPost,
        streamVerifyWorkPost, ArgWord.ofRaw] at hpre h ⊢
      intro iv a c hr hl ht
      have hn := le15 hpre
      have ec := ctxCiph_congr hn fun i hi => hc i (by omega)
      have eh := ctxH_congr fun i hi => hc i (by omega)
      rw [← ec, ← eh] at hr
      rw [bytesAt_tagOut hto, ← ec, ← eh]
      erw [verify_cond fun hok => (recvTag_eq hW hok).symm]
      exact h iv a c (streamRepr_congr (fun i hi => hs i (by omega)) hr) hl ht
  leak := trivial

theorem seal_tagFrame (pb : Nat) :
    sealSig.TagFrame 5 "work" .u64 320 pb (sealPre pb) (sealPost pb) none
      (sealWorkPre pb) (sealWorkPost pb) none where
  pre := fun
    | [_, _, _, _, _, _, _, _], [], _, _, _, _, _, _, _, h => h
  post := fun
    | [ctx, rd, nonce, nl, aad, al, data, len], [], t, W, m₁, m₂, m₃, m', r, _, _, ⟨hag, _⟩, hpre,
        hdis, hto, h => by
      simp only [sealSig, List.take, List.drop, Sig.bufs, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hag hdis
      have hc := agree_of hag.1
      have hn := agree_of hag.2.1
      have ha := agree_of hag.2.2.1
      have hd := agree_of hag.2.2.2
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPre pb) _ m₁ at hpre
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealWorkPost pb) _ m₂ m₃ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₁ m' r
      dsimp only [List.cons_append, List.nil_append, Curry.apply, sealPre, sealPost, sealWorkPost,
        ArgWord.ofRaw] at hpre h ⊢
      have hr := le15 hpre
      have := Nat.mod_le nl.toNat (2 ^ pb)
      have := Nat.mod_le al.toNat (2 ^ pb)
      have := Nat.mod_le len.toNat (2 ^ pb)
      simp only [BitVec.toNat_setWidth] at h ⊢
      rw [bytesAt_tagOut hto, bytesAt_tagOut_sep hto (hdis.2.2.2.sub_left (Region.sub_prefix (by omega))),
        ← ctxCiph_congr hr fun i hi => hc i (by omega), ← ctxH_congr fun i hi => hc i (by omega),
        ← bytesAt_congr fun i hi => hn i (by omega), ← bytesAt_congr fun i hi => ha i (by omega),
        ← bytesAt_congr fun i hi => hd i (by omega)]
      exact h
  leak := trivial

/-- `openResult` reads the received tag only for a length §5.2.1.2 allows. -/
theorem openResult_tag {ciph : Block → Block} {h : Block} {tl : Nat} {iv c a tag₁ tag₂ : List Byte}
    (e : tagLenOk tl → tag₁ = tag₂) :
    openResult ciph h tl iv c a tag₁ = openResult ciph h tl iv c a tag₂ := by
  unfold openResult
  split
  · next hok => rw [e hok]
  · rfl

theorem open_tagFrame (pb : Nat) :
    openSig.TagFrame 5 "work" .u64 320 pb (openPre pb) (openPost pb) (some (openLeak pb))
      (openWorkPre pb) (openWorkPost pb) (some (openWorkLeak pb)) where
  pre := fun
    | [_, _, _, _, _, _, _, _], [_], _, _, _, _, _, _, _, h => h
  post := fun
    | [ctx, rd, nonce, nl, aad, al, data, len], [tl], t, W, m₁, m₂, m₃, m', r, _, _, ⟨hag, hW⟩,
        hpre, hdis, hto, h => by
      simp only [openSig, List.take, List.drop, Sig.bufs, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hag hdis
      have hc := agree_of hag.1
      have hn := agree_of hag.2.1
      have ha := agree_of hag.2.2.1
      have hd := agree_of hag.2.2.2
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPre pb) _ m₁
        at hpre
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openWorkPost pb) _
        m₂ m₃ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
        m₁ m' r
      dsimp only [List.cons_append, List.nil_append, Curry.apply, openPre, openPost, openWorkPost,
        ArgWord.ofRaw] at hpre h ⊢
      have hr := le15 hpre
      have := Nat.mod_le nl.toNat (2 ^ pb)
      have := Nat.mod_le al.toNat (2 ^ pb)
      have := Nat.mod_le len.toNat (2 ^ pb)
      simp only [BitVec.toNat_setWidth] at h ⊢
      rw [openResult_tag fun hok => (recvTag_eq hW hok).symm,
        bytesAt_tagOut_sep hto (hdis.2.2.2.sub_left (Region.sub_prefix (by omega))),
        ← ctxCiph_congr hr fun i hi => hc i (by omega), ← ctxH_congr fun i hi => hc i (by omega),
        ← bytesAt_congr fun i hi => hn i (by omega), ← bytesAt_congr fun i hi => ha i (by omega),
        ← bytesAt_congr fun i hi => hd i (by omega)]
      exact h
  leak := fun
    | [ctx, rd, nonce, nl, aad, al, data, len], [tl], t, W, m₁, m₂, _, _, ⟨hag, hW⟩, hpre => by
      simp only [openSig, List.take, List.drop, Sig.bufs, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hag
      have hc := agree_of hag.1
      have hn := agree_of hag.2.1
      have ha := agree_of hag.2.2.1
      have hd := agree_of hag.2.2.2
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPre pb) _ m₁
        at hpre
      change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openWorkLeak pb) _
        m₂ =
        Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
          ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _ m₁
      dsimp only [List.cons_append, List.nil_append, Curry.apply, openPre, openLeak, openWorkLeak,
        ArgWord.ofRaw] at hpre ⊢
      have hr := le15 hpre
      have := Nat.mod_le nl.toNat (2 ^ pb)
      have := Nat.mod_le al.toNat (2 ^ pb)
      have := Nat.mod_le len.toNat (2 ^ pb)
      simp only [BitVec.toNat_setWidth]
      rw [openResult_tag fun hok => recvTag_eq hW hok,
        ctxCiph_congr hr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
        bytesAt_congr fun i hi => hn i (by omega), bytesAt_congr fun i hi => ha i (by omega),
        bytesAt_congr fun i hi => hd i (by omega)]

end VG.Proof.AesGcm
