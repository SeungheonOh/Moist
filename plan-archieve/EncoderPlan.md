  - ~~Stage 1 – Bit buffer + primitive encoders: introduce a BitBuffer abstraction and helper combinators that allow appending single bits, 4-bit nibbles, and byte-aligned chunks so we can
    mirror the s ⋅ … style recursion from the spec; implement pad/unpad, fixed-width encoders E_n, variable-length natural/integer encoders E_ℕ/E_ℤ, and list encoders E_list following spec/
    flat-serialisation.tex:120-210.~~
  - Stage 2 – ByteString/String/Data primitives: build the chunked bytestring encoder (E_{B*}) that pads before emitting chunk headers, plus UTF-8 string encoder E_{U*} and a helper to turn
    PlutusCore.Data into bytes via εData, all per spec/flat-serialisation.tex:211-320; expose these helpers so both constants and higher layers can call them.
  - Stage 3 – Type + name encoders: map the AtomicType/BuiltinType structure from src/Term.lean:15-43 onto the tag lists shown in spec/flat-serialisation.tex:442-524, emitting [7,…] markers
    for type applications; decide on the name representation (either de Bruijn ℕ or textual String) and implement E_name/E_binder accordingly, referencing the options laid out in spec/flat-
    serialisation.tex:751-788.
  - Stage 4 – Constant encoder: cover every Const constructor in src/Term.lean:46-67, mapping each to the appropriate built-in type encoder defined in spec/flat-serialisation.tex:525-600
    (lists/arrays/pairs recurse on sub-constants, booleans emit a bit, bytes and strings use Stage 2 helpers, data uses E_{B*}, BLS stubs likely leverage fixed-size byte arrays per spec);
    ensure we keep track of both the type tag sequence (E_type) and the value bits.
  - Stage 5 – Builtin function tags: encode BuiltinFun (enumeration at src/Term.lean:70-182) by mapping to the binary tags from the multiple tables in spec/flat-serialisation.tex:600-748;
    centralize this mapping so the encoder just looks up the 7-bit sequence before appending it to the stream.
  - Stage 6 – Term encoder: directly follow the recursive shape mandated in spec/flat-serialisation.tex:362-408, writing a function encodeTerm : BitBuffer → Term → BitBuffer that emits
    the 4-bit tag for each constructor in src/Term.lean:184-195 and then invokes the right helper (E_name, E_constant, E_list_term, etc.); add guardrails for Constr tags < 2^64 and version
    gating for Constr/Case as warned in spec/flat-serialisation.tex:419-440.
  - Stage 7 – Program wrapper & verification: finish with encodeProgram : Program → ByteString that serializes Version (three naturals) and the body, then applies final padding per spec/
    flat-serialisation.tex:333-357; add round-trip/unit tests that encode known programs (e.g., the example in spec/flat-serialisation.tex:811-840) and compare against expected bitstreams,
    plus property-style checks for helper encoders.
