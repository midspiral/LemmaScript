//@ backend dafny
// Pure functional TypeScript domain — all helpers are recursive, no loops

// ═══════════════════════════════════════════════════════════════
// Types
// ═══════════════════════════════════════════════════════════════

type TaskId = number
type ListId = number
type TagId = number
type UserId = string

interface DateVal {
  year: number
  month: number
  day: number
}

interface Task {
  title: string
  notes: string
  completed: boolean
  starred: boolean
  dueDate?: DateVal
  assignees: UserId[]
  tags: TagId[]
  deleted: boolean
  deletedBy?: UserId
  deletedFromList?: ListId
}

interface Tag {
  name: string
}

type ProjectMode = 'Personal' | 'Collaborative'

interface Model {
  mode: ProjectMode
  owner: UserId
  members: UserId[]
  lists: ListId[]
  listNames: Record<number, string>
  tasks: Record<number, TaskId[]>
  taskData: Record<number, Task>
  tags: Record<number, Tag>
  nextListId: number
  nextTaskId: number
  nextTagId: number
}

type Place =
  | { kind: 'AtEnd' }
  | { kind: 'Before'; anchor: TaskId }
  | { kind: 'After'; anchor: TaskId }

type ListPlace =
  | { kind: 'ListAtEnd' }
  | { kind: 'ListBefore'; anchor: ListId }
  | { kind: 'ListAfter'; anchor: ListId }

type Err =
  | 'MissingList' | 'MissingTask' | 'MissingTag' | 'MissingUser'
  | 'DuplicateList' | 'DuplicateTask' | 'DuplicateTag'
  | 'BadAnchor' | 'NotAMember' | 'PersonalProject'
  | 'AlreadyCollaborative' | 'CannotRemoveOwner'
  | 'TaskDeleted' | 'InvalidDate' | 'Rejected'

type Result<T, E> =
  | { ok: true; value: T }
  | { ok: false; error: E }

type Action =
  | { kind: 'NoOp' }
  | { kind: 'AddList'; name: string }
  | { kind: 'RenameList'; listId: ListId; newName: string }
  | { kind: 'DeleteList'; listId: ListId }
  | { kind: 'MoveList'; listId: ListId; listPlace: ListPlace }
  | { kind: 'AddTask'; listId: ListId; title: string }
  | { kind: 'EditTask'; taskId: TaskId; title: string; notes: string }
  | { kind: 'DeleteTask'; taskId: TaskId; userId: UserId }
  | { kind: 'RestoreTask'; taskId: TaskId }
  | { kind: 'MoveTask'; taskId: TaskId; toList: ListId; taskPlace: Place }
  | { kind: 'CompleteTask'; taskId: TaskId }
  | { kind: 'UncompleteTask'; taskId: TaskId }
  | { kind: 'StarTask'; taskId: TaskId }
  | { kind: 'UnstarTask'; taskId: TaskId }
  | { kind: 'SetDueDate'; taskId: TaskId; dueDate?: DateVal }
  | { kind: 'AssignTask'; taskId: TaskId; userId: UserId }
  | { kind: 'UnassignTask'; taskId: TaskId; userId: UserId }
  | { kind: 'AddTagToTask'; taskId: TaskId; tagId: TagId }
  | { kind: 'RemoveTagFromTask'; taskId: TaskId; tagId: TagId }
  | { kind: 'CreateTag'; name: string }
  | { kind: 'RenameTag'; tagId: TagId; newName: string }
  | { kind: 'DeleteTag'; tagId: TagId }
  | { kind: 'MakeCollaborative' }
  | { kind: 'AddMember'; userId: UserId }
  | { kind: 'RemoveMember'; userId: UserId }

export type {
  TaskId, ListId, TagId, UserId,
  DateVal, Task, Tag, ProjectMode, Model,
  Place, ListPlace, Err, Result, Action,
}

// ═══════════════════════════════════════════════════════════════
// Helpers — pure arithmetic
// ═══════════════════════════════════════════════════════════════

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

function eqIgnoreCase(a: string, b: string): boolean {
  //@ havoc
  return a.toLowerCase() === b.toLowerCase()
}

// ═══════════════════════════════════════════════════════════════
// Helpers — pure sequence operations
// ═══════════════════════════════════════════════════════════════

function insertAt<T>(s: T[], i: number, x: T): T[] {
  //@ requires i >= 0 && i <= s.length
  //@ ensures \result.length === s.length + 1
  return [...s.slice(0, i), x, ...s.slice(i)]
}

function posFromPlace(lane: TaskId[], p: Place): number {
  if (p.kind === 'AtEnd') return lane.length
  if (p.kind === 'Before') {
    const idx = lane.indexOf(p.anchor)
    return idx < 0 ? -1 : idx
  }
  const idx = lane.indexOf((p as { kind: 'After'; anchor: TaskId }).anchor)
  return idx < 0 ? -1 : idx + 1
}

function posFromListPlace(lists: ListId[], p: ListPlace): number {
  if (p.kind === 'ListAtEnd') return lists.length
  if (p.kind === 'ListBefore') {
    const idx = lists.indexOf(p.anchor)
    return idx < 0 ? -1 : idx
  }
  const idx = lists.indexOf((p as { kind: 'ListAfter'; anchor: ListId }).anchor)
  return idx < 0 ? -1 : idx + 1
}

// ═══════════════════════════════════════════════════════════════
// Helpers — uniqueness checks (recursive over seq)
// ═══════════════════════════════════════════════════════════════

function listNameExistsFrom(lists: ListId[], listNames: Record<number, string>,
    name: string, excludeList: ListId | undefined, i: number): boolean {
  //@ requires i >= 0 && i <= lists.length
  //@ decreases lists.length - i
  if (i >= lists.length) return false
  const lid = lists[i]
  if (excludeList === undefined || lid !== excludeList) {
    const existing = listNames[lid]
    if (existing !== undefined && eqIgnoreCase(existing, name)) return true
  }
  return listNameExistsFrom(lists, listNames, name, excludeList, i + 1)
}

function listNameExists(m: Model, name: string, excludeList?: ListId): boolean {
  return listNameExistsFrom(m.lists, m.listNames, name, excludeList, 0)
}

function taskTitleExistsFrom(lane: TaskId[], taskData: Record<number, Task>,
    title: string, excludeTask: TaskId | undefined, i: number): boolean {
  //@ requires i >= 0 && i <= lane.length
  //@ decreases lane.length - i
  if (i >= lane.length) return false
  const tid = lane[i]
  if (excludeTask === undefined || tid !== excludeTask) {
    const task = taskData[tid]
    if (task !== undefined && !task.deleted && eqIgnoreCase(task.title, title)) return true
  }
  return taskTitleExistsFrom(lane, taskData, title, excludeTask, i + 1)
}

function taskTitleExistsInList(m: Model, listId: ListId, title: string, excludeTask?: TaskId): boolean {
  const lane = m.tasks[listId]
  if (lane === undefined) return false
  return taskTitleExistsFrom(lane, m.taskData, title, excludeTask, 0)
}

//@ pure
function tagNameExists(m: Model, name: string, excludeTag?: TagId): boolean {
  for (const [tid, tag] of m.tags) {
    if (excludeTag === undefined || tid !== excludeTag) {
      if (eqIgnoreCase(tag.name, name)) return true
    }
  }
  return false
}

export function findListForTaskFrom(lists: ListId[], tasks: Record<number, TaskId[]>,
    taskId: TaskId, i: number): ListId | undefined {
  //@ requires i >= 0 && i <= lists.length
  //@ decreases lists.length - i
  if (i >= lists.length) return undefined
  const lid = lists[i]
  const lane = tasks[lid]
  if (lane !== undefined && lane.includes(taskId)) return lid
  return findListForTaskFrom(lists, tasks, taskId, i + 1)
}

export function findListForTask(m: Model, taskId: TaskId): ListId | undefined {
  return findListForTaskFrom(m.lists, m.tasks, taskId, 0)
}

// ═══════════════════════════════════════════════════════════════
// Helpers — bulk operations (recursive over known key lists)
// ═══════════════════════════════════════════════════════════════

// Remove a task from all lists — iterate over m.lists (known key array)
function removeTaskFromListsFrom(lists: ListId[], tasks: Record<number, TaskId[]>,
    taskId: TaskId, i: number): Record<number, TaskId[]> {
  //@ requires i >= 0 && i <= lists.length
  //@ decreases lists.length - i
  if (i >= lists.length) return tasks
  const lid = lists[i]
  const lane = tasks[lid]
  if (lane !== undefined) {
    return removeTaskFromListsFrom(lists,
      { ...tasks, [lid]: lane.filter(id => id !== taskId) }, taskId, i + 1)
  }
  return removeTaskFromListsFrom(lists, tasks, taskId, i + 1)
}

function removeTaskFromAllLists(lists: ListId[], tasks: Record<number, TaskId[]>,
    taskId: TaskId): Record<number, TaskId[]> {
  return removeTaskFromListsFrom(lists, tasks, taskId, 0)
}

// Remove a key from a Record
function removeKeyFromRecord(rec: Record<number, Task>, key: TaskId): Record<number, Task> {
  const { [key]: _, ...rest } = rec
  return rest
}

// Remove multiple keys from a Record — iterate over keys array
function removeKeysFromRecord(rec: Record<number, Task>,
    keys: TaskId[], i: number): Record<number, Task> {
  //@ requires i >= 0 && i <= keys.length
  //@ decreases keys.length - i
  if (i >= keys.length) return rec
  return removeKeysFromRecord(removeKeyFromRecord(rec, keys[i]), keys, i + 1)
}

// Remove a tag from all tasks — iterates taskData map (no known key list)
//@ pure
function removeTagFromAllTasks(taskData: Record<number, Task>, tagId: TagId): Record<number, Task> {
  const result = new Map<TaskId, Task>()
  //@ havoc
  for (const [tid, task] of taskData) {
    const newTags = task.tags.filter(t => t !== tagId)
    result.set(tid, { ...task, tags: newTags })
  }
  //@ as Record
  return result
}

// Clear an assignee from all tasks — iterates taskData map (no known key list)
//@ pure
function clearAssigneeFromAllTasks(taskData: Record<number, Task>, userId: UserId): Record<number, Task> {
  const result = new Map<TaskId, Task>()
  //@ havoc
  for (const [tid, task] of taskData) {
    const newAssignees = task.assignees.filter(u => u !== userId)
    result.set(tid, { ...task, assignees: newAssignees })
  }
  //@ as Record
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
    members: [INITIAL_OWNER],
    lists: [],
    listNames: {},
    tasks: {},
    taskData: {},
    tags: {},
    nextListId: 0,
    nextTaskId: 0,
    nextTagId: 0,
  }
}

//@ __mapFromArray
export function apply(m: Model, a: Action): Result<Model, Err> {
  switch (a.kind) {

  case 'NoOp':
    return ok(m)

  case 'AddList': {
    if (listNameExists(m, a.name)) return err('DuplicateList')
    const id = m.nextListId
    return ok({
      ...m,
      lists: [...m.lists, id],
      listNames: { ...m.listNames, [id]: a.name },
      tasks: { ...m.tasks, [id]: [] as TaskId[] },
      nextListId: m.nextListId + 1,
    })
  }

  case 'RenameList': {
    if (!m.lists.includes(a.listId)) return err('MissingList')
    if (listNameExists(m, a.newName, a.listId)) return err('DuplicateList')
    return ok({ ...m, listNames: { ...m.listNames, [a.listId]: a.newName } })
  }

  case 'DeleteList': {
    if (!m.lists.includes(a.listId)) return ok(m)
    const lane = m.tasks[a.listId] || []
    const newTaskData = removeKeysFromRecord(m.taskData, lane, 0)
    const newLists = m.lists.filter(l => l !== a.listId)
    const { [a.listId]: _ln, ...newListNames } = m.listNames
    const { [a.listId]: _tk, ...newTasks } = m.tasks
    return ok({
      ...m,
      lists: newLists,
      listNames: newListNames,
      tasks: newTasks,
      taskData: newTaskData,
    })
  }

  case 'MoveList': {
    if (!m.lists.includes(a.listId)) return err('MissingList')
    const pos = posFromListPlace(m.lists, a.listPlace)
    if (pos < 0) return err('BadAnchor')
    const without = m.lists.filter(l => l !== a.listId)
    const clamped = Math.min(pos, without.length)
    return ok({ ...m, lists: insertAt(without, clamped, a.listId) })
  }

  case 'AddTask': {
    if (!m.lists.includes(a.listId)) return err('MissingList')
    if (taskTitleExistsInList(m, a.listId, a.title)) return err('DuplicateTask')
    const id = m.nextTaskId
    const task: Task = {
      title: a.title, notes: '', completed: false, starred: false,
      assignees: [], tags: [], deleted: false,
    }
    const lane = m.tasks[a.listId] || []
    return ok({
      ...m,
      tasks: { ...m.tasks, [a.listId]: [...lane, id] },
      taskData: { ...m.taskData, [id]: task },
      nextTaskId: m.nextTaskId + 1,
    })
  }

  case 'EditTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    const listId = findListForTask(m, a.taskId)
    if (listId !== undefined && taskTitleExistsInList(m, listId, a.title, a.taskId)) {
      return err('DuplicateTask')
    }
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, title: a.title, notes: a.notes } } })
  }

  case 'DeleteTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return ok(m)
    if (task.deleted) return ok(m)
    const listId = findListForTask(m, a.taskId)
    const newTasks = removeTaskFromAllLists(m.lists, m.tasks, a.taskId)
    return ok({ ...m, tasks: newTasks, taskData: { ...m.taskData, [a.taskId]: { ...task, deleted: true, deletedBy: a.userId, deletedFromList: listId } } })
  }

  case 'RestoreTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (!task.deleted) return err('MissingTask')
    if (m.lists.length === 0) return err('MissingList')
    const targetList = task.deletedFromList !== undefined && m.lists.includes(task.deletedFromList)
      ? task.deletedFromList : m.lists[0]
    if (taskTitleExistsInList(m, targetList, task.title)) return err('DuplicateTask')
    const lane = m.tasks[targetList] || []
    return ok({
      ...m,
      tasks: { ...m.tasks, [targetList]: [...lane, a.taskId] },
      taskData: { ...m.taskData, [a.taskId]: { ...task, deleted: false, deletedBy: undefined, deletedFromList: undefined } },
    })
  }

  case 'MoveTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (!m.lists.includes(a.toList)) return err('MissingList')
    if (taskTitleExistsInList(m, a.toList, task.title, a.taskId)) return err('DuplicateTask')
    const cleaned = removeTaskFromAllLists(m.lists, m.tasks, a.taskId)
    const targetLane = cleaned[a.toList] || []
    const pos = posFromPlace(targetLane, a.taskPlace)
    if (pos < 0) return err('BadAnchor')
    const clamped = Math.min(pos, targetLane.length)
    const newLane = insertAt(targetLane, clamped, a.taskId)
    return ok({ ...m, tasks: { ...cleaned, [a.toList]: newLane } })
  }

  case 'CompleteTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, completed: true } } })
  }

  case 'UncompleteTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, completed: false } } })
  }

  case 'StarTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, starred: true } } })
  }

  case 'UnstarTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, starred: false } } })
  }

  case 'SetDueDate': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (a.dueDate !== undefined && !validDate(a.dueDate)) return err('InvalidDate')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, dueDate: a.dueDate } } })
  }

  case 'AssignTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (!m.members.includes(a.userId)) return err('NotAMember')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, assignees: [...task.assignees, a.userId] } } })
  }

  case 'UnassignTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, assignees: task.assignees.filter(u => u !== a.userId) } } })
  }

  case 'AddTagToTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    if (!(a.tagId in m.tags)) return err('MissingTag')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, tags: [...task.tags, a.tagId] } } })
  }

  case 'RemoveTagFromTask': {
    const task = m.taskData[a.taskId]
    if (task === undefined) return err('MissingTask')
    if (task.deleted) return err('TaskDeleted')
    return ok({ ...m, taskData: { ...m.taskData, [a.taskId]: { ...task, tags: task.tags.filter(t => t !== a.tagId) } } })
  }

  case 'CreateTag': {
    if (tagNameExists(m, a.name)) return err('DuplicateTag')
    const id = m.nextTagId
    return ok({ ...m, tags: { ...m.tags, [id]: { name: a.name } }, nextTagId: m.nextTagId + 1 })
  }

  case 'RenameTag': {
    if (!(a.tagId in m.tags)) return err('MissingTag')
    if (tagNameExists(m, a.newName, a.tagId)) return err('DuplicateTag')
    return ok({ ...m, tags: { ...m.tags, [a.tagId]: { name: a.newName } } })
  }

  case 'DeleteTag': {
    if (!(a.tagId in m.tags)) return ok(m)
    const newTaskData = removeTagFromAllTasks(m.taskData, a.tagId)
    const { [a.tagId]: _tg, ...newTags } = m.tags
    return ok({ ...m, taskData: newTaskData, tags: newTags })
  }

  case 'MakeCollaborative':
    if (m.mode === 'Collaborative') return ok(m)
    return ok({ ...m, mode: 'Collaborative' })

  case 'AddMember': {
    if (m.mode === 'Personal') return err('PersonalProject')
    if (m.members.includes(a.userId)) return ok(m)
    return ok({ ...m, members: [...m.members, a.userId] })
  }

  case 'RemoveMember': {
    if (a.userId === m.owner) return err('CannotRemoveOwner')
    if (!m.members.includes(a.userId)) return ok(m)
    const newTaskData = clearAssigneeFromAllTasks(m.taskData, a.userId)
    return ok({ ...m, members: m.members.filter(u => u !== a.userId), taskData: newTaskData })
  }

  }
}

// ═══════════════════════════════════════════════════════════════
// Rebase
// ═══════════════════════════════════════════════════════════════

function degradeIfAnchorMoved(movedId: TaskId, p: Place): Place {
  if (p.kind === 'AtEnd') return p
  if (p.kind === 'Before') return p.anchor === movedId ? { kind: 'AtEnd' } : p
  return (p as { kind: 'After'; anchor: TaskId }).anchor === movedId ? { kind: 'AtEnd' } : p
}

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
  if (remote.kind === 'RemoveMember' && local.kind === 'AssignTask') {
    return remote.userId === local.userId ? { kind: 'NoOp' } : local
  }
  if (remote.kind === 'MoveList' && local.kind === 'MoveList') {
    return remote.listId === local.listId ? { kind: 'NoOp' } : local
  }
  if (remote.kind === 'MoveTask' && local.kind === 'MoveTask') {
    if (remote.taskId === local.taskId) return local
    return {
      kind: 'MoveTask',
      taskId: local.taskId,
      toList: local.toList,
      taskPlace: degradeIfAnchorMoved(remote.taskId, local.taskPlace),
    }
  }
  return local
}

export function rebase(remote: Action, local: Action): Action {
  if (remote.kind === 'NoOp') return local
  if (local.kind === 'NoOp') return local
  if (remote.kind === 'DeleteTask') return rebaseAgainstDelete(remote.taskId, local)
  return rebaseOther(remote, local)
}

export function candidates(_m: unknown, a: Action): Action[] {
  if (a.kind === 'MoveTask' && a.taskPlace.kind !== 'AtEnd') {
    return [a, { ...a, taskPlace: { kind: 'AtEnd' } }]
  }
  if (a.kind === 'MoveList' && a.listPlace.kind !== 'ListAtEnd') {
    return [a, { ...a, listPlace: { kind: 'ListAtEnd' } }]
  }
  return [a]
}

// ═══════════════════════════════════════════════════════════════
// Views
// ═══════════════════════════════════════════════════════════════

export function isPriorityTask(t: Task): boolean {
  return t.starred && !t.completed && !t.deleted
}

export function isLogbookTask(t: Task): boolean {
  return t.completed && !t.deleted
}

export function isVisibleTask(t: Task): boolean {
  return !t.deleted
}

export function getTask(m: Model, taskId: TaskId): Task | undefined {
  const t = m.taskData[taskId]
  if (t === undefined) return undefined
  return t.deleted ? undefined : t
}

export function getTaskIncludingDeleted(m: Model, taskId: TaskId): Task | undefined {
  return m.taskData[taskId]
}

function getTasksInListFrom(lane: TaskId[], taskData: Record<number, Task>, i: number): TaskId[] {
  //@ requires i >= 0 && i <= lane.length
  //@ decreases lane.length - i
  if (i >= lane.length) return []
  const task = taskData[lane[i]]
  if (task !== undefined && !task.deleted) {
    return [lane[i], ...getTasksInListFrom(lane, taskData, i + 1)]
  }
  return getTasksInListFrom(lane, taskData, i + 1)
}

export function getTasksInList(m: Model, listId: ListId): TaskId[] {
  //@ ensures \result.length >= 0
  const lane = m.tasks[listId]
  if (lane === undefined) return []
  return getTasksInListFrom(lane, m.taskData, 0)
}

export function getListName(m: Model, listId: ListId): string | undefined {
  return m.listNames[listId]
}

export function getLists(m: Model): ListId[] {
  return m.lists
}

export function getTagName(m: Model, tagId: TagId): string | undefined {
  const tag = m.tags[tagId]
  if (tag === undefined) return undefined
  return tag.name
}

//@ pure
export function countPriorityTasks(m: Model): number {
  //@ ensures \result >= 0
  let count = 0
  for (const [, task] of m.taskData) {
    if (isPriorityTask(task)) count = count + 1
  }
  return count
}

//@ pure
export function countLogbookTasks(m: Model): number {
  //@ ensures \result >= 0
  let count = 0
  for (const [, task] of m.taskData) {
    if (isLogbookTask(task)) count = count + 1
  }
  return count
}
