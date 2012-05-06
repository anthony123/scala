/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 */

package org.objectweb.asm;

import org.objectweb.asm.Attribute;

/**
 * A subclass of ASM's Attribute for the sole purpose of accessing a protected field there.
 *
 */
public class CustomAttr extends Attribute {

    public CustomAttr(final String type, final byte[] value) {
        super(type);
        /* The next line depends on asm-4.0.jar ie the shrinked version.
           When using, say, asm-debug-all-4.0.jar, the assignment should read `super.value = value;` */
        super.b = value;
    }

}
