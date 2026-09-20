import «leftPad.def»

prove_correct leftPad by
  velvet_vcgen [leftPad] with finish [String.length_append]
