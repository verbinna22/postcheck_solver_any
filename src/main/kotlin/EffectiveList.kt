package ru.mylogininya

data class EffectiveList(val length: Int = 0, val root: EffectiveNode? = null) {
    fun addFirst(data: String): EffectiveList {
        return EffectiveList(length + 1, EffectiveNode(data, root))
    }

    fun addInOrder(data: EffectiveList): EffectiveList {
        val elems = data.getDataAsFrom()
        var r = root
        var l = length
        for (elem in elems) {
            l += 1
            r = EffectiveNode(elem, r)
        }
        return EffectiveList(l, r)
    }

    fun addReversed(data: EffectiveList): EffectiveList {
        val elems = data.getDataAsTo()
        var r = root
        var l = length
        for (elem in elems) {
            l += 1
            r = EffectiveNode(elem, r)
        }
        return EffectiveList(l, r)
    }

    fun removeFirst(): EffectiveList? {
        if (length == 0) return null
        if (length == 1) return EffectiveList()
        return EffectiveList(length - 1, root!!.next)
    }

    fun removeLast(): EffectiveList? {
        if (length == 0) return null
        return EffectiveList(length - 1, root)
    }

    fun getDataAsTo(): List<String> {
        val res = mutableListOf<String>()
        var node = root
        (0 until length).forEach { _ ->
            res.add(node!!.data)
            node = node.next
        }
        return res
    }

    fun getDataAsFrom(): List<String> {
        return (getDataAsTo() as MutableList<String>).also { it.reverse() }
    }
}

data class EffectiveNode(val data: String, val next: EffectiveNode?)
