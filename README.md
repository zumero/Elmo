
# What is this?

It's a prototype implementation of an embeddable Mongo-compatible database for
use in mobile apps.

This is *not* ready for production use.

For more info, see the blog entry at 
[http://www.ericsink.com/entries/mobile\_sync\_for\_mongo.html](http://www.ericsink.com/entries/mobile_sync_for_mongo.html).

# What's the license?

GPLv3

# Isn't the GPL incompatible with the App Store?

Yes, that's why we're using it (for now).  

Until this implementation matures, we just want this code to be
visible, not used.  We'll revisit licensing issues later.

# Why is this written in F#?

Because it's an exploratory prototype, and that was the fastest way to
develop it.

# Will this stay in F# as the only implementation?

If Apple and Google deprecate all their tooling and standardize on Xamarin
for all mobile development, yes.  :-)

Otherwise, this would need to get ported and/or reimplemented in something
else so that people building apps with ObjC or Java could use it.

# Why are you building this?

As part of our exploration of mobile sync solutions for Mongo.

For more info, see the blog entry mentioned near the top of this README.  

# Why is this called Elmo?

It stands for Embeddable Lite Mongo.

# How complete is this?

Most CRUD operations work just like they do in Mongo.

Intentionally omitted:  Sharding, JavaScript

Not done yet:  Full text search, geo, indexes

Number of passing test cases in jstests:  Over 300

For more info, see the blog entry mentioned near the top of this README.  

# How can you be running Mongo's jstests on an "embedded" database?  

Elmo has a server which was written specifically for that purpose.

