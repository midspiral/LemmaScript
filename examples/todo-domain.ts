//@ backend dafny

// ═══════════════════════════════════════════════════════════════
// Types
// ═══════════════════════════════════════════════════════════════

// Core ID types
type TaskId = number
type ListId = number
type TagId = number
type UserId = string

// Date with validation
interface DateVal {
  year: number
  month: number
  day: number
}

// Task data
interface Task {
  title: string
  notes: string
  completed: boolean
  starred: boolean
  dueDate?: DateVal
  assignees: Set<UserId>
  tags: Set<TagId>
  deleted: boolean
  deletedBy?: UserId
  deletedFromList?: ListId
}

// Tag data
interface Tag {
  name: string
}

// Project collaboration mode
type ProjectMode = 'Personal' | 'Collaborative'

// The Model represents a single project's state
interface Model {
  mode: ProjectMode
  owner: UserId
  members: Set<UserId>
  lists: ListId[]
  listNames: Map<ListId, string>
  tasks: Map<ListId, TaskId[]>
  taskData: Map<TaskId, Task>
  tags: Map<TagId, Tag>
  nextListId: number
  nextTaskId: number
  nextTagId: number
}

// Anchor-based placement
type Place =
  | { kind: 'AtEnd' }
  | { kind: 'Before'; anchor: TaskId }
  | { kind: 'After'; anchor: TaskId }

type ListPlace =
  | { kind: 'ListAtEnd' }
  | { kind: 'ListBefore'; anchor: ListId }
  | { kind: 'ListAfter'; anchor: ListId }

// Error types
type Err =
  | 'MissingList'
  | 'MissingTask'
  | 'MissingTag'
  | 'MissingUser'
  | 'DuplicateList'
  | 'DuplicateTask'
  | 'DuplicateTag'
  | 'BadAnchor'
  | 'NotAMember'
  | 'PersonalProject'
  | 'AlreadyCollaborative'
  | 'CannotRemoveOwner'
  | 'TaskDeleted'
  | 'InvalidDate'
  | 'Rejected'

// Result type
type Result<T, E> =
  | { ok: true; value: T }
  | { ok: false; error: E }

// Actions
type Action =
  | { kind: 'NoOp' }
  // List CRUD
  | { kind: 'AddList'; name: string }
  | { kind: 'RenameList'; listId: ListId; newName: string }
  | { kind: 'DeleteList'; listId: ListId }
  | { kind: 'MoveList'; listId: ListId; listPlace: ListPlace }
  // Task CRUD
  | { kind: 'AddTask'; listId: ListId; title: string }
  | { kind: 'EditTask'; taskId: TaskId; title: string; notes: string }
  | { kind: 'DeleteTask'; taskId: TaskId; userId: UserId }
  | { kind: 'RestoreTask'; taskId: TaskId }
  | { kind: 'MoveTask'; taskId: TaskId; toList: ListId; taskPlace: Place }
  // Task status
  | { kind: 'CompleteTask'; taskId: TaskId }
  | { kind: 'UncompleteTask'; taskId: TaskId }
  | { kind: 'StarTask'; taskId: TaskId }
  | { kind: 'UnstarTask'; taskId: TaskId }
  // Due date
  | { kind: 'SetDueDate'; taskId: TaskId; dueDate?: DateVal }
  // Assignment
  | { kind: 'AssignTask'; taskId: TaskId; userId: UserId }
  | { kind: 'UnassignTask'; taskId: TaskId; userId: UserId }
  // Tags on tasks
  | { kind: 'AddTagToTask'; taskId: TaskId; tagId: TagId }
  | { kind: 'RemoveTagFromTask'; taskId: TaskId; tagId: TagId }
  // Tag CRUD
  | { kind: 'CreateTag'; name: string }
  | { kind: 'RenameTag'; tagId: TagId; newName: string }
  | { kind: 'DeleteTag'; tagId: TagId }
  // Project mode
  | { kind: 'MakeCollaborative' }
  // Membership
  | { kind: 'AddMember'; userId: UserId }
  | { kind: 'RemoveMember'; userId: UserId }

export type {
  TaskId, ListId, TagId, UserId,
  DateVal, Task, Tag, ProjectMode, Model,
  Place, ListPlace, Err, Result, Action,
}

// ═══════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════

// ── Date validation ──────────────────────────────────────────

export function isLeapYear(year: number): boolean {

  return (year % 4 === 0 && year % 100 !== 0) || (year % 400 === 0)
}

export function daysInMonth(month: number, year: number): number {

  //@ ensures \result >= 0
  if (month === 1) return 31
  if (month === 2) return isLeapYear(year) ? 29 : 28
  if (month === 3) return 31
  if (month === 4) return 30
  if (month === 5) return 31
  if (month === 6) return 30
  if (month === 7) return 31
  if (month === 8) return 31
  if (month === 9) return 30
  if (month === 10) return 31
  if (month === 11) return 30
  if (month === 12) return 31
  return 0
}

export function validDate(d: DateVal): boolean {

  return d.year >= 1970 && d.month >= 1 && d.month <= 12 &&
    d.day >= 1 && d.day <= daysInMonth(d.month, d.year)
}

// ── String helpers ───────────────────────────────────────────

export function toLowerChar(c: string): string {

  //@ havoc
  return c.toLowerCase()
}

export function eqIgnoreCase(a: string, b: string): boolean {

  //@ havoc
  return a.toLowerCase() === b.toLowerCase()
}

// ── Sequence helpers ─────────────────────────────────────────

export function seqContains<T>(s: T[], x: T): boolean {
  //@ type T (==)
  let i = 0
  while (i < s.length) {
    //@ invariant i >= 0 && i <= s.length
    if (s[i] === x) return true
    i = i + 1
  }
  return false
}

export function indexOf<T>(s: T[], x: T): number {
  //@ type T (==)
  //@ ensures \result >= -1 && \result < s.length
  let i = 0
  while (i < s.length) {
    //@ invariant i >= 0 && i <= s.length
    if (s[i] === x) return i
    i = i + 1
  }
  return -1
}

export function removeFirst<T>(s: T[], x: T): T[] {
  //@ type T (==)
  //@ ensures \result.length <= s.length
  if (s.length === 0) return []
  if (s[0] === x) return s.slice(1)
  return [s[0], ...removeFirst(s.slice(1), x)]
}

export function insertAt<T>(s: T[], i: number, x: T): T[] {

  //@ requires i >= 0 && i <= s.length
  //@ ensures \result.length === s.length + 1
  return [...s.slice(0, i), x, ...s.slice(i)]
}

// ── Position calculation ─────────────────────────────────────

export function posFromPlace(lane: TaskId[], p: Place): number {

  if (p.kind === 'AtEnd') return lane.length
  if (p.kind === 'Before') {
    const idx = indexOf(lane, p.anchor)
    return idx < 0 ? -1 : idx
  }
  // After
  const idx = indexOf(lane, (p as { kind: 'After'; anchor: TaskId }).anchor)
  return idx < 0 ? -1 : idx + 1
}

export function posFromListPlace(lists: ListId[], p: ListPlace): number {

  if (p.kind === 'ListAtEnd') return lists.length
  if (p.kind === 'ListBefore') {
    const idx = indexOf(lists, p.anchor)
    return idx < 0 ? -1 : idx
  }
  // ListAfter
  const idx = indexOf(lists, (p as { kind: 'ListAfter'; anchor: ListId }).anchor)
  return idx < 0 ? -1 : idx + 1
}

// ── Uniqueness checks ────────────────────────────────────────

export function listNameExists(m: Model, name: string, excludeList?: ListId): boolean {

  let i = 0
  while (i < m.lists.length) {
    //@ invariant i >= 0 && i <= m.lists.length
    const lid = m.lists[i]
    if (excludeList === undefined || lid !== excludeList) {
      const existingName = m.listNames.get(lid)
      if (existingName !== undefined && eqIgnoreCase(existingName, name)) return true
    }
    i = i + 1
  }
  return false
}

export function taskTitleExistsInList(m: Model, listId: ListId, title: string, excludeTask?: TaskId): boolean {

  const lane = m.tasks.get(listId)
  if (lane === undefined) return false
  let i = 0
  while (i < lane.length) {
    //@ invariant i >= 0 && i <= lane.length
    const tid = lane[i]
    if (excludeTask === undefined || tid !== excludeTask) {
      const task = m.taskData.get(tid)
      if (task !== undefined && !task.deleted && eqIgnoreCase(task.title, title)) return true
    }
    i = i + 1
  }
  return false
}

export function tagNameExists(m: Model, name: string, excludeTag?: TagId): boolean {

  //@ havoc
  for (const [tid, tag] of m.tags) {
    if (excludeTag === undefined || tid !== excludeTag) {
      if (eqIgnoreCase(tag.name, name)) return true
    }
  }
  return false
}

// ── Task location ────────────────────────────────────────────

export function findListForTask(m: Model, taskId: TaskId): ListId | undefined {

  let i = 0
  while (i < m.lists.length) {
    //@ invariant i >= 0 && i <= m.lists.length
    const lid = m.lists[i]
    const lane = m.tasks.get(lid)
    if (lane !== undefined && seqContains(lane, taskId)) return lid
    i = i + 1
  }
  return undefined
}

// ── Bulk operations ──────────────────────────────────────────

export function removeTaskFromAllLists(tasks: Map<ListId, TaskId[]>, taskId: TaskId): Map<ListId, TaskId[]> {

  const result = new Map<ListId, TaskId[]>()
  //@ havoc
  for (const [lid, lane] of tasks) {
    result.set(lid, lane.filter(id => id !== taskId))
  }
  return result
}

export function removeTagFromAllTasks(taskData: Map<TaskId, Task>, tagId: TagId): Map<TaskId, Task> {

  const result = new Map<TaskId, Task>()
  //@ havoc
  for (const [tid, task] of taskData) {
    const newTags = new Set(task.tags)
    newTags.delete(tagId)
    result.set(tid, { ...task, tags: newTags })
  }
  return result
}

export function clearAssigneeFromAllTasks(taskData: Map<TaskId, Task>, userId: UserId): Map<TaskId, Task> {

  const result = new Map<TaskId, Task>()
  //@ havoc
  for (const [tid, task] of taskData) {
    const newAssignees = new Set(task.assignees)
    newAssignees.delete(userId)
    result.set(tid, { ...task, assignees: newAssignees })
  }
  return result
}

// ═══════════════════════════════════════════════════════════════
// Apply (state transitions)
// ═══════════════════════════════════════════════════════════════

function ok(m: Model): Result<Model, Err> { return { ok: true, value: m } }
function err(e: Err): Result<Model, Err> { return { ok: false, error: e } }

const INITIAL_OWNER: UserId = '__initial__'

export function init(): Model {

  return {
    mode: 'Personal',
    owner: INITIAL_OWNER,
    members: new Set([INITIAL_OWNER]),
    lists: [],
    listNames: new Map(),
    tasks: new Map(),
    taskData: new Map(),
    tags: new Map(),
    nextListId: 0,
    nextTaskId: 0,
    nextTagId: 0,
  }
}

export function apply(m: Model, a: Action): Result<Model, Err> {

  switch (a.kind) {

  case 'NoOp':
    return ok(m)

  case 'AddList': {
    if (listNameExists(m, a.name)) return err('DuplicateList')
    const id = m.nextListId
    const newLists = [...m.lists, id]
    const newListNames = new Map(m.listNames)
    newListNames.set(id, a.name)
    const newTasks = new Map(m.tasks)
    newTasks.set(id, [])
    return ok({
      ...m,
      lists: newLists,
      listNames: newListNames,
      tasks: newTasks,
      nextListId: m.nextListId + 1,
    })
  }

  case 'RenameList': {
    if (!seqContains(m.lists, a.listId)) return err('MissingList')
    if (listNameExists(m, a.newName, a.listId)) return err('DuplicateList')
    const newListNames = new Map(m.listNames)
    newListNames.set(a.listId, a.newName)
    return ok({ ...m, listNames: newListNames })
  }

  case 'DeleteList': {
    if (!seqContains(m.lists, a.listId)) return ok(m) // idempotent
    const lane = m.tasks.get(a.listId) || []
    // Remove all tasks in this list from taskData
    const newTaskData = new Map(m.taskData)
    for (const tid of lane) {
      newTaskData.delete(tid)
    }
    const newLists = m.lists.filter(l => l !== a.listId)
    const newListNames = new Map(m.listNames)
    newListNames.delete(a.listId)
    const newTasks = new Map(m.tasks)
    newTasks.delete(a.listId)
    return ok({
      ...m,
      lists: newLists,
      listNames: newListNames,
      tasks: newTasks,
      taskData: newTaskData,
    })
  }

  case 'MoveList': {
    if (!seqContains(m.lists, a.listId)) return err('MissingList')
    const pos = posFromListPlace(m.lists, a.listPlace)
    if (pos < 0) return err('BadAnchor')
    const without = m.lists.filter(l => l !== a.listId)
    const clamped = Math.min(pos, without.length)
    const newLists = insertAt(without, clamped, a.listId)
    return ok({ ...m, lists: newLists })
  }

  case 'AddTask': {
    if (!seqContains(m.lists, a.listId)) return err('MissingList')
    if (taskTitleExistsInList(m, a.listId, a.title)) return err('DuplicateTask')
    const id = m.nextTaskId
    const task: Task = {
      title: a.title,
      notes: '',
      completed: false,
      starred: false,
      assignees: new Set(),
      tags: new Set(),
      deleted: false,
    }
    const lane = m.tasks.get(a.listId) || []
    const newTasks = new Map(m.tasks)
    newTasks.set(a.listId, [...lane, id])
    const newTaskData = new Map(m.taskData)
    newTaskData.set(id, task)
    return ok({
      ...m,
      tasks: newTasks,
      taskData: newTaskData,
      nextTaskId: m.nextTaskId + 1,
    })
  }

  case 'EditTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const listId = findListForTask(m, a.taskId)
    if (listId !== undefined && taskTitleExistsInList(m, listId, a.title, a.taskId)) {
      return err('DuplicateTask')
    }
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, title: a.title, notes: a.notes })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'DeleteTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return ok(m) // idempotent
    if (task.deleted) return ok(m)       // already deleted
    const listId = findListForTask(m, a.taskId)
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, {
      ...task,
      deleted: true,
      deletedBy: a.userId,
      deletedFromList: listId,
    })
    const newTasks = removeTaskFromAllLists(m.tasks, a.taskId)
    return ok({ ...m, tasks: newTasks, taskData: newTaskData })
  }

  case 'RestoreTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (!task.deleted) return err('MissingTask')
    if (m.lists.length === 0) return err('MissingList')
    // Restore to original list if it exists, otherwise first list
    const targetList = task.deletedFromList !== undefined && seqContains(m.lists, task.deletedFromList)
      ? task.deletedFromList
      : m.lists[0]
    if (taskTitleExistsInList(m, targetList, task.title)) return err('DuplicateTask')
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, {
      ...task,
      deleted: false,
      deletedBy: undefined,
      deletedFromList: undefined,
    })
    const lane = m.tasks.get(targetList) || []
    const newTasks = new Map(m.tasks)
    newTasks.set(targetList, [...lane, a.taskId])
    return ok({ ...m, tasks: newTasks, taskData: newTaskData })
  }

  case 'MoveTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (!seqContains(m.lists, a.toList)) return err('MissingList')
    if (taskTitleExistsInList(m, a.toList, task.title, a.taskId)) return err('DuplicateTask')
    // Remove from all lists
    const cleaned = removeTaskFromAllLists(m.tasks, a.taskId)
    // Insert at new position
    const targetLane = cleaned.get(a.toList) || []
    const pos = posFromPlace(targetLane, a.taskPlace)
    if (pos < 0) return err('BadAnchor')
    const clamped = Math.min(pos, targetLane.length)
    const newLane = insertAt(targetLane, clamped, a.taskId)
    const newTasks = new Map(cleaned)
    newTasks.set(a.toList, newLane)
    return ok({ ...m, tasks: newTasks })
  }

  case 'CompleteTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, completed: true })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'UncompleteTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, completed: false })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'StarTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, starred: true })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'UnstarTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, starred: false })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'SetDueDate': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (a.dueDate !== undefined && !validDate(a.dueDate)) return err('InvalidDate')
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, dueDate: a.dueDate })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'AssignTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (!m.members.has(a.userId)) return err('NotAMember')
    const newAssignees = new Set(task.assignees)
    newAssignees.add(a.userId)
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, assignees: newAssignees })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'UnassignTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const newAssignees = new Set(task.assignees)
    newAssignees.delete(a.userId)
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, assignees: newAssignees })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'AddTagToTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (!m.tags.has(a.tagId)) return err('MissingTag')
    const newTags = new Set(task.tags)
    newTags.add(a.tagId)
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, tags: newTags })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'RemoveTagFromTask': {
    const task = m.taskData.get(a.taskId)
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const newTags = new Set(task.tags)
    newTags.delete(a.tagId)
    const newTaskData = new Map(m.taskData)
    newTaskData.set(a.taskId, { ...task, tags: newTags })
    return ok({ ...m, taskData: newTaskData })
  }

  case 'CreateTag': {
    if (tagNameExists(m, a.name)) return err('DuplicateTag')
    const id = m.nextTagId
    const newTags = new Map(m.tags)
    newTags.set(id, { name: a.name })
    return ok({ ...m, tags: newTags, nextTagId: m.nextTagId + 1 })
  }

  case 'RenameTag': {
    if (!m.tags.has(a.tagId)) return err('MissingTag')
    if (tagNameExists(m, a.newName, a.tagId)) return err('DuplicateTag')
    const newTags = new Map(m.tags)
    newTags.set(a.tagId, { name: a.newName })
    return ok({ ...m, tags: newTags })
  }

  case 'DeleteTag': {
    if (!m.tags.has(a.tagId)) return ok(m) // idempotent
    const newTaskData = removeTagFromAllTasks(m.taskData, a.tagId)
    const newTags = new Map(m.tags)
    newTags.delete(a.tagId)
    return ok({ ...m, taskData: newTaskData, tags: newTags })
  }

  case 'MakeCollaborative': {
    if (m.mode === 'Collaborative') return ok(m) // idempotent
    return ok({ ...m, mode: 'Collaborative' })
  }

  case 'AddMember': {
    if (m.mode === 'Personal') return err('PersonalProject')
    if (m.members.has(a.userId)) return ok(m) // idempotent
    const newMembers = new Set(m.members)
    newMembers.add(a.userId)
    return ok({ ...m, members: newMembers })
  }

  case 'RemoveMember': {
    if (a.userId === m.owner) return err('CannotRemoveOwner')
    if (!m.members.has(a.userId)) return ok(m) // idempotent
    const newTaskData = clearAssigneeFromAllTasks(m.taskData, a.userId)
    const newMembers = new Set(m.members)
    newMembers.delete(a.userId)
    return ok({ ...m, members: newMembers, taskData: newTaskData })
  }

  }
}

// ═══════════════════════════════════════════════════════════════
// Rebase (conflict resolution / operational transformation)
// ═══════════════════════════════════════════════════════════════

// ── Anchor degradation ───────────────────────────────────────

function degradeIfAnchorMoved(movedId: TaskId, p: Place): Place {

  if (p.kind === 'AtEnd') return p
  if (p.kind === 'Before') {
    return p.anchor === movedId ? { kind: 'AtEnd' } : p
  }
  // After
  return (p as { kind: 'After'; anchor: TaskId }).anchor === movedId
    ? { kind: 'AtEnd' }
    : p
}

// ── Rebase: transform local action given remote action ───────

function rebaseAgainstDelete(remoteTaskId: TaskId, local: Action): Action {
  switch (local.kind) {
    case 'EditTask':          return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'MoveTask':          return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'CompleteTask':      return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'UncompleteTask':    return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'StarTask':          return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'UnstarTask':        return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'SetDueDate':        return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'AssignTask':        return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'UnassignTask':      return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'AddTagToTask':      return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    case 'RemoveTagFromTask': return local.taskId === remoteTaskId ? { kind: 'NoOp' } : local
    default: return local
  }
}

function rebaseOther(remote: Action, local: Action): Action {
  // RemoveMember trumps assignment to that user
  if (remote.kind === 'RemoveMember' && local.kind === 'AssignTask') {
    return remote.userId === local.userId ? { kind: 'NoOp' } : local
  }

  // MoveList: remote wins for same list
  if (remote.kind === 'MoveList' && local.kind === 'MoveList') {
    return remote.listId === local.listId ? { kind: 'NoOp' } : local
  }

  // MoveTask: same task = keep local (LWW); different task = degrade anchor
  if (remote.kind === 'MoveTask' && local.kind === 'MoveTask') {
    if (remote.taskId === local.taskId) return local
    return {
      kind: 'MoveTask',
      taskId: local.taskId,
      toList: local.toList,
      taskPlace: degradeIfAnchorMoved(remote.taskId, local.taskPlace),
    }
  }

  // Default: keep local
  return local
}

export function rebase(remote: Action, local: Action): Action {
  if (remote.kind === 'NoOp') return local
  if (local.kind === 'NoOp') return local
  if (remote.kind === 'DeleteTask') return rebaseAgainstDelete(remote.taskId, local)
  return rebaseOther(remote, local)
}

// ── Candidates: retry alternatives for failed placement ──────

export function candidates(m: unknown, a: Action): Action[] {

  if (a.kind === 'MoveTask' && a.taskPlace.kind !== 'AtEnd') {
    return [
      a,
      { ...a, taskPlace: { kind: 'AtEnd' } },
    ]
  }
  if (a.kind === 'MoveList' && a.listPlace.kind !== 'ListAtEnd') {
    return [
      a,
      { ...a, listPlace: { kind: 'ListAtEnd' } },
    ]
  }
  return [a]
}

// ═══════════════════════════════════════════════════════════════
// Views (queries / smart lists)
// ═══════════════════════════════════════════════════════════════

// ── Smart list predicates ────────────────────────────────────

export function isPriorityTask(t: Task): boolean {

  return t.starred && !t.completed && !t.deleted
}

export function isLogbookTask(t: Task): boolean {

  return t.completed && !t.deleted
}

export function isVisibleTask(t: Task): boolean {

  return !t.deleted
}

// ── Query functions ──────────────────────────────────────────

export function getTask(m: Model, taskId: TaskId): Task | undefined {

  const t = m.taskData.get(taskId)
  if (t === undefined) return undefined
  return t.deleted ? undefined : t
}

export function getTaskIncludingDeleted(m: Model, taskId: TaskId): Task | undefined {

  return m.taskData.get(taskId)
}

export function getTasksInList(m: Model, listId: ListId): TaskId[] {

  //@ ensures \result.length >= 0
  const lane = m.tasks.get(listId)
  if (lane === undefined) return []
  // Filter to visible tasks
  const result: TaskId[] = []
  let i = 0
  while (i < lane.length) {
    //@ invariant i >= 0 && i <= lane.length
    //@ invariant result.length <= i
    const task = m.taskData.get(lane[i])
    if (task !== undefined && !task.deleted) {
      result.push(lane[i])
    }
    i = i + 1
  }
  return result
}

export function getListName(m: Model, listId: ListId): string | undefined {

  return m.listNames.get(listId)
}

export function getLists(m: Model): ListId[] {

  return m.lists
}

export function getTagName(m: Model, tagId: TagId): string | undefined {

  return m.tags.get(tagId)?.name
}

export function countPriorityTasks(m: Model): number {

  //@ ensures \result >= 0
  let count = 0
  //@ havoc
  for (const [, task] of m.taskData) {
    if (isPriorityTask(task)) count = count + 1
  }
  return count
}

export function countLogbookTasks(m: Model): number {

  //@ ensures \result >= 0
  let count = 0
  //@ havoc
  for (const [, task] of m.taskData) {
    if (isLogbookTask(task)) count = count + 1
  }
  return count
}
