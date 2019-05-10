/*
 * Copyright (c) 2000, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.net.spi.nameservice;

public interface NameServiceDescriptor {
    /**
     * Create a new instance of the corresponding name service.
     */
    public NameService createNameService () throws Exception ;

    /**
     * Returns this service provider's name
     *
     */
    public String getProviderName();

    /**
     * Returns this name service type
     * "dns" "nis" etc
     */
    public String getType();
}
