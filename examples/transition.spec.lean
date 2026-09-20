import «transition.types»

@[grind, simp]
def lastEvent (events : Array Event) : Event :=
  events[events.size - 1]!
