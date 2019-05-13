package org.omg.PortableInterceptor;


/**
* org/omg/PortableInterceptor/AdapterManagerIdHelper.java .
* Generated by the IDL-to-Java compiler (portable), version "3.2"
* from ../../../../src/share/classes/org/omg/PortableInterceptor/Interceptors.idl
* Wednesday, February 2, 2011 6:12:11 PM GMT-08:00
*/


/** Adapter manager identifier.  Every object adapter has an adapter manager,
   * indicated in this API only through the ID.  A group of object adapter
   * instances may share the same adapter manager, in which case state transitions
   * reported for the adapter manager are observed by all object adapters with the
   * same adapter manager ID.
   */
abstract public class AdapterManagerIdHelper
{
  private static String  _id = "IDL:omg.org/PortableInterceptor/AdapterManagerId:1.0";

  public static void insert (org.omg.CORBA.Any a, int that)
  {
    org.omg.CORBA.portable.OutputStream out = a.create_output_stream ();
    a.type (type ());
    write (out, that);
    a.read_value (out.create_input_stream (), type ());
  }

  public static int extract (org.omg.CORBA.Any a)
  {
    return read (a.create_input_stream ());
  }

  private static org.omg.CORBA.TypeCode __typeCode = null;
  synchronized public static org.omg.CORBA.TypeCode type ()
  {
    if (__typeCode == null)
    {
      __typeCode = org.omg.CORBA.ORB.init ().get_primitive_tc (org.omg.CORBA.TCKind.tk_long);
      __typeCode = org.omg.CORBA.ORB.init ().create_alias_tc (org.omg.PortableInterceptor.AdapterManagerIdHelper.id (), "AdapterManagerId", __typeCode);
    }
    return __typeCode;
  }

  public static String id ()
  {
    return _id;
  }

  public static int read (org.omg.CORBA.portable.InputStream istream)
  {
    int value = (int)0;
    value = istream.read_long ();
    return value;
  }

  public static void write (org.omg.CORBA.portable.OutputStream ostream, int value)
  {
    ostream.write_long (value);
  }

}
