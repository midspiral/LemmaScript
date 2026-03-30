import «transition.types»

@[grind, loomAbstractionSimp]
def lastEvent (events : Array Event) : Event :=
  events[events.size - 1]!
